//! CNF -> UVL recovery (any2uvl). Parses a DIMACS file, builds an
//! implication graph, detects OR/XOR groups, assigns a shallowest-parent
//! tree via BFS, and optionally runs a greedy CTC-reduction pass. Reuses
//! builder.HInfo/ChildEdge/GroupEntry so cnf.hierarchyToCnf can compute
//! residual CTCs unchanged.

const std = @import("std");
const Allocator = std.mem.Allocator;
const builder_mod = @import("builder.zig");
const HInfo = builder_mod.HInfo;
const ChildEdge = builder_mod.ChildEdge;
const ChildType = builder_mod.ChildType;
const GroupEntry = builder_mod.GroupEntry;
const cnf = @import("cnf.zig");
const subsumption = @import("subsumption.zig");
const lexer = @import("lexer.zig");
const parser_mod = @import("parser.zig");
const constraint = @import("constraint.zig");

fn absLess(_: void, a: i32, b: i32) bool {
    return @abs(a) < @abs(b);
}

fn sortByAbs(clause: []i32) void {
    std.mem.sort(i32, clause, {}, absLess);
}

/// Hashes/compares clauses by content. Clauses must be pre-sorted with
/// sortByAbs before use as a key.
pub const ClauseSetContext = struct {
    pub fn hash(_: @This(), key: []const i32) u64 {
        var h: u64 = 0xcbf29ce484222325;
        for (key) |v| {
            const bytes = std.mem.asBytes(&v);
            for (bytes) |b| {
                h ^= b;
                h *%= 0x100000001b3;
            }
        }
        return h;
    }
    pub fn eql(_: @This(), a: []const i32, b: []const i32) bool {
        return std.mem.eql(i32, a, b);
    }
};

pub const ClauseSet = std.HashMap([]const i32, void, ClauseSetContext, std.hash_map.default_max_load_percentage);

fn containsI32(haystack: []const i32, needle: i32) bool {
    for (haystack) |v| {
        if (v == needle) return true;
    }
    return false;
}

fn setAdd(alloc: Allocator, list: *std.ArrayList(i32), v: i32) !void {
    if (containsI32(list.items, v)) return;
    try list.append(alloc, v);
}

// ---------------------------------------------------------------------------
// difflib.SequenceMatcher.ratio() port, for --byname's parent tie-break.
// ---------------------------------------------------------------------------

const MatchSpan = struct { i: usize, ahi: usize, j: usize, bhi: usize };

fn findLongestMatch(a: []const u8, alo: usize, ahi: usize, b: []const u8, blo: usize, bhi: usize, j2len: []usize, newj2len: []usize) struct { i: usize, j: usize, size: usize } {
    @memset(j2len, 0);
    var besti = alo;
    var bestj = blo;
    var bestsize: usize = 0;
    var i = alo;
    while (i < ahi) : (i += 1) {
        @memset(newj2len, 0);
        var j = blo;
        while (j < bhi) : (j += 1) {
            if (b[j] != a[i]) continue;
            const prev: usize = if (j == 0) 0 else j2len[j - 1];
            const k = prev + 1;
            newj2len[j] = k;
            if (k > bestsize) {
                besti = i + 1 - k;
                bestj = j + 1 - k;
                bestsize = k;
            }
        }
        @memcpy(j2len, newj2len);
    }
    return .{ .i = besti, .j = bestj, .size = bestsize };
}

/// Port of difflib.SequenceMatcher(None, a, b).ratio(): 2*M / (len(a)+len(b)),
/// M being the total length of matching blocks found by repeatedly taking
/// the longest common contiguous run and recursing into the remainders.
/// No junk-element filtering.
fn ratio(alloc: Allocator, a: []const u8, b: []const u8) !f64 {
    const total_len = a.len + b.len;
    if (total_len == 0) return 1.0;
    if (a.len == 0 or b.len == 0) return 0.0;

    const j2len = try alloc.alloc(usize, b.len);
    const newj2len = try alloc.alloc(usize, b.len);

    var stack = std.ArrayList(MatchSpan).empty;
    try stack.append(alloc, .{ .i = 0, .ahi = a.len, .j = 0, .bhi = b.len });

    var total_matched: usize = 0;
    while (stack.pop()) |frame| {
        if (frame.i >= frame.ahi or frame.j >= frame.bhi) continue;
        const m = findLongestMatch(a, frame.i, frame.ahi, b, frame.j, frame.bhi, j2len, newj2len);
        if (m.size == 0) continue;
        total_matched += m.size;
        if (frame.i < m.i and frame.j < m.j) {
            try stack.append(alloc, .{ .i = frame.i, .ahi = m.i, .j = frame.j, .bhi = m.j });
        }
        if (m.i + m.size < frame.ahi and m.j + m.size < frame.bhi) {
            try stack.append(alloc, .{ .i = m.i + m.size, .ahi = frame.ahi, .j = m.j + m.size, .bhi = frame.bhi });
        }
    }

    return 2.0 * @as(f64, @floatFromInt(total_matched)) / @as(f64, @floatFromInt(total_len));
}

fn stripQuotesLower(alloc: Allocator, s: []const u8) ![]const u8 {
    var inner = s;
    if (inner.len >= 2 and inner[0] == '"' and inner[inner.len - 1] == '"') {
        inner = inner[1 .. inner.len - 1];
    }
    const out = try alloc.alloc(u8, inner.len);
    for (inner, 0..) |c, i| out[i] = std.ascii.toLower(c);
    return out;
}

// ---------------------------------------------------------------------------
// DIMACS parsing
// ---------------------------------------------------------------------------

pub const ParsedDimacs = struct {
    id_to_name: std.AutoHashMap(i32, []const u8),
    name_to_id: std.StringHashMap(i32),
    clauses: std.ArrayList([]i32),
};

pub const ParseDimacsError = error{ OutOfMemory, NoHeader };

/// Parses `c <id> <name>` comments (quoting bare multi-word names for
/// third-party DIMACS files), the `p cnf <nv> <nc>` header's variable
/// count, and clauses (each sorted by abs value). Also synthesizes a
/// placeholder name ("F<id>") for every variable id in `[1, nv]` that has
/// no `c <id> <name>` comment -- `nv` here is the max of the header's
/// declared count and every id actually seen (in a comment or a clause
/// literal), since a hand-written or third-party DIMACS file's header can
/// undercount its variable count. This guarantees every variable the file
/// could possibly reference has a name, so a fully free/unconstrained
/// variable (no clause, no comment) is never silently invisible to the
/// caller, and no variable-without-a-comment ever causes an `id_to_name`
/// lookup to fail downstream.
///
/// A `p` line must be present at all -- its absence means this isn't a
/// DIMACS file (e.g. it's UVL or SMT-LIB text), and returns `NoHeader`
/// rather than silently parsing whatever numeric-looking lines it finds.
pub fn parseDimacs(alloc: Allocator, text: []const u8) ParseDimacsError!ParsedDimacs {
    var id_to_name = std.AutoHashMap(i32, []const u8).init(alloc);
    var name_to_id = std.StringHashMap(i32).init(alloc);
    var clauses = std.ArrayList([]i32).empty;
    var header_nv: i32 = 0;
    var max_seen_id: i32 = 0;

    var saw_header = false;

    var lines = std.mem.splitScalar(u8, text, '\n');
    while (lines.next()) |line_raw| {
        const line = std.mem.trimEnd(u8, line_raw, "\r");
        if (line.len == 0) continue;

        if (line[0] == 'c') {
            var it = std.mem.tokenizeAny(u8, line[1..], " \t");
            const id_str = it.next() orelse continue;
            const id = std.fmt.parseInt(i32, id_str, 10) catch continue;
            const rest = std.mem.trim(u8, it.rest(), " \t");
            if (rest.len == 0) continue;

            var name = rest;
            if (!(name.len >= 2 and name[0] == '"' and name[name.len - 1] == '"')) {
                if (std.mem.indexOfScalar(u8, name, ' ') != null) {
                    name = try std.fmt.allocPrint(alloc, "\"{s}\"", .{name});
                }
            }
            try id_to_name.put(id, name);
            try name_to_id.put(name, id);
            if (id > max_seen_id) max_seen_id = id;
            continue;
        }

        if (line[0] == 'p') {
            saw_header = true;
            var it = std.mem.tokenizeAny(u8, line[1..], " \t");
            _ = it.next(); // "cnf"
            if (it.next()) |nv_str| {
                header_nv = std.fmt.parseInt(i32, nv_str, 10) catch 0;
            }
            continue;
        }

        var lits = std.ArrayList(i32).empty;
        var it = std.mem.tokenizeAny(u8, line, " \t");
        while (it.next()) |tok| {
            const v = std.fmt.parseInt(i32, tok, 10) catch continue;
            if (v == 0) continue;
            try lits.append(alloc, v);
            const av: i32 = @intCast(@abs(v));
            if (av > max_seen_id) max_seen_id = av;
        }
        if (lits.items.len == 0) continue;
        const owned = try lits.toOwnedSlice(alloc);
        sortByAbs(owned);
        try clauses.append(alloc, owned);
    }

    if (!saw_header) return ParseDimacsError.NoHeader;

    const nv = @max(header_nv, max_seen_id);
    var id: i32 = 1;
    while (id <= nv) : (id += 1) {
        if (id_to_name.contains(id)) continue;
        const name = try std.fmt.allocPrint(alloc, "F{d}", .{id});
        try id_to_name.put(id, name);
        try name_to_id.put(name, id);
    }

    return .{ .id_to_name = id_to_name, .name_to_id = name_to_id, .clauses = clauses };
}

// ---------------------------------------------------------------------------
// Implication graph + OR/XOR group detection
// ---------------------------------------------------------------------------

pub const Graph = struct {
    implies: std.AutoHashMap(i32, std.ArrayList(i32)),
    implied_by: std.AutoHashMap(i32, std.ArrayList(i32)),
    groups: std.AutoHashMap(i32, std.ArrayList(i32)), // parent id -> member ids
};

fn getOrPutList(map: *std.AutoHashMap(i32, std.ArrayList(i32)), key: i32) !*std.ArrayList(i32) {
    const gop = try map.getOrPut(key);
    if (!gop.found_existing) gop.value_ptr.* = std.ArrayList(i32).empty;
    return gop.value_ptr;
}

/// Builds the implication graph and detects OR/XOR groups. A member set is
/// only accepted as a real group if exactly one candidate parent claims it
/// and every member individually implies that parent; this rejects a plain
/// "P => (A|B)" cross-tree constraint being mistaken for a group.
pub fn buildGraph(alloc: Allocator, clauses: []const []i32) !Graph {
    var implies = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);
    var implied_by = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);

    var group_candidates = std.HashMap([]const i32, std.ArrayList(i32), ClauseSetContext, std.hash_map.default_max_load_percentage).init(alloc);

    for (clauses) |clause| {
        if (clause.len == 2) {
            // Clauses are sorted by absolute value, so the negative and
            // positive literal aren't reliably clause[0]/clause[1].
            var neg: ?i32 = null;
            var pos: ?i32 = null;
            for (clause) |lit| {
                if (lit < 0) neg = lit else pos = lit;
            }
            if (neg) |a| {
                if (pos) |b| {
                    if (@abs(a) != b) {
                        const l = try getOrPutList(&implies, @intCast(@abs(a)));
                        try setAdd(alloc, l, b);
                    }
                }
            }
        } else if (clause.len > 2) {
            var negs: usize = 0;
            var parent: i32 = 0;
            var members = std.ArrayList(i32).empty;
            for (clause) |lit| {
                if (lit < 0) {
                    negs += 1;
                    parent = -lit;
                } else {
                    try members.append(alloc, lit);
                }
            }
            if (negs != 1) continue;
            if (containsI32(members.items, parent)) continue; // tautological clause

            const key = try members.toOwnedSlice(alloc);
            sortByAbs(key);
            const gop = try group_candidates.getOrPut(key);
            if (!gop.found_existing) gop.value_ptr.* = std.ArrayList(i32).empty;
            try gop.value_ptr.append(alloc, parent);
        }
    }

    var groups = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);
    var gc_it = group_candidates.iterator();
    while (gc_it.next()) |entry| {
        const members = entry.key_ptr.*;
        const candidate_parents = entry.value_ptr.*;
        if (candidate_parents.items.len != 1) continue;
        const parent = candidate_parents.items[0];

        var all_imply = true;
        for (members) |m| {
            const implied = implies.get(m) orelse std.ArrayList(i32).empty;
            if (!containsI32(implied.items, parent)) {
                all_imply = false;
                break;
            }
        }
        if (!all_imply) continue;

        var group_members = std.ArrayList(i32).empty;
        for (members) |m| try group_members.append(alloc, m);
        try groups.put(parent, group_members);
    }

    var it = implies.iterator();
    while (it.next()) |entry| {
        const child = entry.key_ptr.*;
        for (entry.value_ptr.items) |parent| {
            const l = try getOrPutList(&implied_by, parent);
            try setAdd(alloc, l, child);
        }
    }

    return .{ .implies = implies, .implied_by = implied_by, .groups = groups };
}

// ---------------------------------------------------------------------------
// Level 2 (experimental, opt-in): propagation-based implication recovery
// ---------------------------------------------------------------------------
//
// `buildGraph` above only ever finds a child=>parent edge if the literal
// 2-literal clause `{-child, parent}` is still present. A global
// subsumption/simplification pass (see docs/pipeline_clause_dedup.md) can
// remove that exact clause while leaving the *implication* semantically
// true (e.g. `parent` turns out to be forced true unconditionally by other
// clauses, so `{-child, parent}` is subsumed by the unit clause `{parent}`
// and dropped -- child=>parent still holds, vacuously). This section
// recovers such edges by checking actual logical entailment via unit
// propagation (BCP) instead of pattern-matching a literal clause shape:
// for each candidate feature, assume it selected and propagate; every
// other feature forced true as a consequence is a genuine (checked, not
// guessed) implication edge, regardless of which clauses happen to survive
// syntactically.
//
// This is naturally more expensive than the literal-clause scan (one BCP
// pass per candidate feature, each O(clause literals touched)), so it's
// gated behind `infer_propagation`, off by default -- see `recover`'s
// `infer_propagation` parameter and any2uvl's `--propagate` flag. Intended
// to be benchmarked before ever turning it on by default.

const Occ = std.AutoHashMap(i32, std.ArrayList(usize));

fn occBuild(alloc: Allocator, map: *Occ, lit_var: i32, clause_idx: usize) !void {
    const l = try getOrPutOcc(map, lit_var);
    try l.append(alloc, clause_idx);
}

fn getOrPutOcc(map: *Occ, key: i32) !*std.ArrayList(usize) {
    const gop = try map.getOrPut(key);
    if (!gop.found_existing) gop.value_ptr.* = std.ArrayList(usize).empty;
    return gop.value_ptr;
}

const PropagationState = struct {
    remaining: []usize,
    satisfied: []bool,
    assigned: []i8, // indexed by var id, 1..nv; 0 = unassigned, 1 = true, -1 = false
};

/// Runs unit propagation starting from `start`, mutating `state` in place.
/// Returns the list of variable ids forced *true* during this call
/// (including any of `start`'s own positive literals), or `null` on a
/// conflict (the assumption is inconsistent with the rest of the CNF).
fn propagate(alloc: Allocator, clauses: []const []const i32, pos_occ: *Occ, neg_occ: *Occ, state: *PropagationState, start: []const i32) !?[]i32 {
    var queue = std.ArrayList(i32).empty;
    for (start) |lit| {
        const v: usize = @intCast(@abs(lit));
        const val: i8 = if (lit > 0) 1 else -1;
        if (state.assigned[v] != 0) {
            if (state.assigned[v] != val) return null;
            continue;
        }
        state.assigned[v] = val;
        try queue.append(alloc, lit);
    }

    var forced_true = std.ArrayList(i32).empty;
    var qi: usize = 0;
    while (qi < queue.items.len) : (qi += 1) {
        const lit = queue.items[qi];
        const v: usize = @intCast(@abs(lit));
        const is_pos = lit > 0;
        if (is_pos) try forced_true.append(alloc, @intCast(v));

        if ((if (is_pos) pos_occ else neg_occ).getPtr(@intCast(v))) |list| {
            for (list.items) |ci| state.satisfied[ci] = true;
        }

        if ((if (is_pos) neg_occ else pos_occ).getPtr(@intCast(v))) |list| {
            for (list.items) |ci| {
                if (state.satisfied[ci]) continue;
                state.remaining[ci] -= 1;
                if (state.remaining[ci] == 0) return null;
                if (state.remaining[ci] == 1) {
                    for (clauses[ci]) |l2| {
                        const v2: usize = @intCast(@abs(l2));
                        if (state.assigned[v2] != 0) continue;
                        state.assigned[v2] = if (l2 > 0) 1 else -1;
                        try queue.append(alloc, l2);
                        break;
                    }
                }
            }
        }
    }
    return try forced_true.toOwnedSlice(alloc);
}

/// Augments `graph.implies`/`graph.implied_by` with edges recovered via
/// unit propagation (see section doc comment above). `nv` bounds the
/// variable id range to try (every id in `id_to_name`, i.e. every
/// declared feature per the Level 1 completeness fix in `parseDimacs`).
pub fn augmentGraphWithPropagation(alloc: Allocator, graph: *Graph, clauses: []const []i32, nv: i32) !void {
    var pos_occ = Occ.init(alloc);
    var neg_occ = Occ.init(alloc);
    for (clauses, 0..) |c, ci| {
        for (c) |lit| {
            if (lit > 0) try occBuild(alloc, &pos_occ, lit, ci) else try occBuild(alloc, &neg_occ, -lit, ci);
        }
    }

    var base = PropagationState{
        .remaining = try alloc.alloc(usize, clauses.len),
        .satisfied = try alloc.alloc(bool, clauses.len),
        .assigned = try alloc.alloc(i8, @intCast(nv + 1)),
    };
    for (clauses, 0..) |c, ci| base.remaining[ci] = c.len;
    @memset(base.satisfied, false);
    @memset(base.assigned, 0);

    var units = std.ArrayList(i32).empty;
    for (clauses) |c| {
        if (c.len == 1) try units.append(alloc, c[0]);
    }
    if (try propagate(alloc, clauses, &pos_occ, &neg_occ, &base, units.items) == null) {
        return; // base unit set is self-contradictory (CNF is UNSAT); bail out safely, add nothing
    }

    // Reused scratch buffers for every candidate below: `scratch_alloc` (see
    // `recover`'s doc comment) is an arena that's only torn down once, at
    // the very end -- allocating a fresh clause-count-sized copy per
    // candidate via `alloc.dupe` (the original approach here) is O(nv)
    // such buffers alive simultaneously, i.e. O(nv * clauses.len) total
    // memory, which OOM-killed a real run on automotive02v4.uvl (18616
    // features x ~368K clauses x 3 buffers -> tens of GB). Allocating once
    // and `@memcpy`-resetting from `base` each iteration keeps this at
    // O(clauses.len + nv) for the whole function, not per candidate.
    const remaining = try alloc.alloc(usize, clauses.len);
    const satisfied = try alloc.alloc(bool, clauses.len);
    const assigned = try alloc.alloc(i8, @intCast(nv + 1));

    var new_implies = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);
    var id: i32 = 1;
    while (id <= nv) : (id += 1) {
        if (base.assigned[@intCast(id)] != 0) continue; // already pinned unconditionally; nothing to learn

        @memcpy(remaining, base.remaining);
        @memcpy(satisfied, base.satisfied);
        @memcpy(assigned, base.assigned);
        var state = PropagationState{ .remaining = remaining, .satisfied = satisfied, .assigned = assigned };

        const forced = try propagate(alloc, clauses, &pos_occ, &neg_occ, &state, &[_]i32{id}) orelse continue;
        for (forced) |w| {
            if (w == id) continue;
            const l = try getOrPutList(&new_implies, id);
            try setAdd(alloc, l, w);
        }
    }

    // Merge into graph.implies (literal-clause edges take precedence
    // automatically since setAdd is idempotent either way), then rebuild
    // implied_by from scratch to stay consistent.
    var nit = new_implies.iterator();
    while (nit.next()) |entry| {
        const l = try getOrPutList(&graph.implies, entry.key_ptr.*);
        for (entry.value_ptr.items) |w| try setAdd(alloc, l, w);
    }

    var implied_by = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);
    var iit = graph.implies.iterator();
    while (iit.next()) |entry| {
        const child = entry.key_ptr.*;
        for (entry.value_ptr.items) |parent| {
            const l = try getOrPutList(&implied_by, parent);
            try setAdd(alloc, l, child);
        }
    }
    graph.implied_by = implied_by;
}

// ---------------------------------------------------------------------------
// BFS depths + parent selection
// ---------------------------------------------------------------------------

pub const ParentKind = enum { group, mandatory, optional };
pub const ParentInfo = struct { parent: i32, kind: ParentKind };

pub const DepthsResult = struct {
    depths: std.AutoHashMap(i32, i32),
    parents: std.AutoHashMap(i32, ParentInfo),
};

/// BFS shortest-path depths, then per-feature parent selection over the
/// shortest-depth candidates: prefer a group edge, then a mandatory
/// (biconditional) edge, then the name-similarity-best (--byname) or
/// numerically-smallest optional candidate.
pub fn findDepths(alloc: Allocator, root: i32, graph: *const Graph, id_to_name: *const std.AutoHashMap(i32, []const u8), by_name: bool) !DepthsResult {
    var depths = std.AutoHashMap(i32, i32).init(alloc);
    try depths.put(root, 0);

    var queue = std.ArrayList(i32).empty;
    try queue.append(alloc, root);
    var qi: usize = 0;
    while (qi < queue.items.len) : (qi += 1) {
        const f = queue.items[qi];
        const d = depths.get(f).?;
        if (graph.implied_by.get(f)) |children| {
            const sorted_children = try alloc.dupe(i32, children.items);
            std.mem.sort(i32, sorted_children, {}, std.sort.asc(i32));
            for (sorted_children) |child| {
                if (!depths.contains(child)) {
                    try depths.put(child, d + 1);
                    try queue.append(alloc, child);
                }
            }
        }
    }

    var parents = std.AutoHashMap(i32, ParentInfo).init(alloc);
    var it = depths.iterator();
    while (it.next()) |entry| {
        const feature = entry.key_ptr.*;
        if (feature == root) continue;
        const d = entry.value_ptr.*;

        const cand_source = graph.implies.get(feature) orelse continue;
        var candidates = std.ArrayList(i32).empty;
        for (cand_source.items) |p| {
            if (depths.get(p)) |pd| {
                if (pd == d - 1) try candidates.append(alloc, p);
            }
        }
        if (candidates.items.len == 0) continue;

        var group_cands = std.ArrayList(i32).empty;
        for (candidates.items) |p| {
            if (graph.groups.get(p)) |members| {
                if (containsI32(members.items, feature)) try group_cands.append(alloc, p);
            }
        }
        if (group_cands.items.len > 0) {
            try parents.put(feature, .{ .parent = std.mem.min(i32, group_cands.items), .kind = .group });
            continue;
        }

        var mand_cands = std.ArrayList(i32).empty;
        for (candidates.items) |p| {
            if (graph.implies.get(p)) |pset| {
                if (containsI32(pset.items, feature)) try mand_cands.append(alloc, p);
            }
        }
        if (mand_cands.items.len > 0) {
            try parents.put(feature, .{ .parent = std.mem.min(i32, mand_cands.items), .kind = .mandatory });
            continue;
        }

        var best: i32 = candidates.items[0];
        if (by_name) {
            const child_name = try stripQuotesLower(alloc, id_to_name.get(feature) orelse "");
            var best_ratio: f64 = -1.0;
            for (candidates.items) |p| {
                const pname = try stripQuotesLower(alloc, id_to_name.get(p) orelse "");
                const r = try ratio(alloc, child_name, pname);
                if (r > best_ratio) {
                    best_ratio = r;
                    best = p;
                }
            }
        } else {
            best = std.mem.min(i32, candidates.items);
        }
        try parents.put(feature, .{ .parent = best, .kind = .optional });
    }

    return .{ .depths = depths, .parents = parents };
}

// ---------------------------------------------------------------------------
// Hierarchy construction (from `parents`/`groups` -> HInfo tree)
// ---------------------------------------------------------------------------

const ChildRef = struct { id: i32, mandatory: bool };

pub const BuiltHierarchy = struct {
    hierarchy: std.StringHashMap(HInfo),
    root_name: []const u8,
};

fn isXorGroup(clause_set: *const ClauseSet, member_ids: []const i32, alloc: Allocator) !bool {
    var i: usize = 0;
    while (i < member_ids.len) : (i += 1) {
        var j = i + 1;
        while (j < member_ids.len) : (j += 1) {
            const pair = try alloc.alloc(i32, 2);
            pair[0] = -member_ids[i];
            pair[1] = -member_ids[j];
            sortByAbs(pair);
            if (!clause_set.contains(pair)) return false;
        }
    }
    return true;
}

const WalkFrame = struct { id: i32, parent_name: ?[]const u8, kind: ChildType, is_group_member: bool };

/// Drains `stack` into `hierarchy`, following parents2childs/groups edges.
/// Shared by `buildHierarchy`'s initial walk from `root` and its leftover-
/// grafting pass below.
fn drainHierarchyStack(alloc: Allocator, hierarchy: *std.StringHashMap(HInfo), stack: *std.ArrayList(WalkFrame), parents2childs: *const std.AutoHashMap(i32, std.ArrayList(ChildRef)), groups: *const std.AutoHashMap(i32, std.ArrayList(i32)), id_to_name: *const std.AutoHashMap(i32, []const u8), clause_set: *const ClauseSet) !void {
    while (stack.pop()) |frame| {
        const name = id_to_name.get(frame.id).?;
        if (frame.parent_name) |pname| {
            if (!frame.is_group_member) {
                const info = hierarchy.getPtr(pname).?;
                try info.children.append(alloc, .{ .name = name, .kind = frame.kind });
            }
        }
        if (hierarchy.contains(name)) continue;
        try hierarchy.put(name, HInfo{ .parent = frame.parent_name });

        if (parents2childs.get(frame.id)) |childs| {
            var k = childs.items.len;
            while (k > 0) {
                k -= 1;
                const c = childs.items[k];
                try stack.append(alloc, .{ .id = c.id, .parent_name = name, .kind = if (c.mandatory) .mandatory else .optional, .is_group_member = false });
            }
        }

        if (groups.get(frame.id)) |member_ids| {
            const is_xor = try isXorGroup(clause_set, member_ids.items, alloc);
            const g = try alloc.create(GroupEntry);
            g.* = .{ .kind = if (is_xor) .xor_group else .or_group };
            const info = hierarchy.getPtr(name).?;
            for (member_ids.items) |mid| {
                const mname = id_to_name.get(mid).?;
                try g.members.append(alloc, mname);
                try info.children.append(alloc, .{ .name = mname, .kind = .optional });
            }
            try info.groups.append(alloc, g);

            var k = member_ids.items.len;
            while (k > 0) {
                k -= 1;
                const mid = member_ids.items[k];
                try stack.append(alloc, .{ .id = mid, .parent_name = name, .kind = .optional, .is_group_member = true });
            }
        }
    }
}

/// True iff `id` is targeted by a parents2childs/groups edge whose source
/// is itself in `ids` -- i.e. it has a predecessor within the leftover
/// set, so it'll be reached once that predecessor is grafted and doesn't
/// need its own direct graft under root.
fn hasLeftoverPredecessor(id: i32, ids: *const std.AutoHashMap(i32, void), parents2childs: *const std.AutoHashMap(i32, std.ArrayList(ChildRef)), groups: *const std.AutoHashMap(i32, std.ArrayList(i32))) bool {
    var it = ids.keyIterator();
    while (it.next()) |src_ptr| {
        const src = src_ptr.*;
        if (parents2childs.get(src)) |childs| {
            for (childs.items) |c| {
                if (c.id == id) return true;
            }
        }
        if (groups.get(src)) |members| {
            if (containsI32(members.items, id)) return true;
        }
    }
    return false;
}

/// Builds the HInfo tree from parents2childs/groups. Group members are
/// also added as plain (optional) children, matching a real UVL group's
/// CNF encoding where each member gets its own "member => parent" edge in
/// addition to the group clause, same shape builder.zig's startFeature
/// produces for a real parse. A feature's content is only built once; it
/// can still be reached (and referenced) via more than one path.
///
/// Every id in `id_to_name` is guaranteed to end up in the returned
/// hierarchy: any id the root traversal never reaches (a fully free
/// variable with no clauses, or one whose only path from root was broken
/// by a subsumption-eliminated edge) is grafted directly under root as an
/// optional child instead of being silently dropped from the recovered
/// model. Grafting picks only the "entry points" of each leftover
/// connected component (ids with no predecessor within the leftover set
/// itself), so a leftover subtree is attached once at its top, not
/// re-listed node-by-node under root.
pub fn buildHierarchy(alloc: Allocator, root: i32, parents2childs: *const std.AutoHashMap(i32, std.ArrayList(ChildRef)), groups: *const std.AutoHashMap(i32, std.ArrayList(i32)), id_to_name: *const std.AutoHashMap(i32, []const u8), clause_set: *const ClauseSet) !BuiltHierarchy {
    var hierarchy = std.StringHashMap(HInfo).init(alloc);
    const root_name = id_to_name.get(root).?;

    var stack = std.ArrayList(WalkFrame).empty;
    try stack.append(alloc, .{ .id = root, .parent_name = null, .kind = .optional, .is_group_member = false });
    try drainHierarchyStack(alloc, &hierarchy, &stack, parents2childs, groups, id_to_name, clause_set);

    var leftover = std.AutoHashMap(i32, void).init(alloc);
    var id_it = id_to_name.iterator();
    while (id_it.next()) |e| {
        const id = e.key_ptr.*;
        if (id == root) continue;
        if (!hierarchy.contains(e.value_ptr.*)) try leftover.put(id, {});
    }

    if (leftover.count() > 0) {
        var graft_ids = std.ArrayList(i32).empty;
        var lit = leftover.keyIterator();
        while (lit.next()) |id_ptr| {
            if (!hasLeftoverPredecessor(id_ptr.*, &leftover, parents2childs, groups)) {
                try graft_ids.append(alloc, id_ptr.*);
            }
        }
        // Pathological case (a cycle entirely within the leftover set, so
        // every id has a predecessor): fall back to grafting everything
        // rather than dropping the whole component.
        if (graft_ids.items.len == 0) {
            var lit2 = leftover.keyIterator();
            while (lit2.next()) |id_ptr| try graft_ids.append(alloc, id_ptr.*);
        }
        std.mem.sort(i32, graft_ids.items, {}, std.sort.asc(i32));
        for (graft_ids.items) |gid| {
            try stack.append(alloc, .{ .id = gid, .parent_name = root_name, .kind = .optional, .is_group_member = false });
        }
        try drainHierarchyStack(alloc, &hierarchy, &stack, parents2childs, groups, id_to_name, clause_set);
    }

    return .{ .hierarchy = hierarchy, .root_name = root_name };
}

// ---------------------------------------------------------------------------
// Serialization
// ---------------------------------------------------------------------------

const SerFrame = union(enum) {
    node: struct { name: []const u8, indent: usize },
    text: struct { indent: usize, text: []const u8 },
};

fn writeIndentLine(w: *std.Io.Writer, indent: usize, text: []const u8) !void {
    try w.splatByteAll(' ', indent * 4);
    try w.writeAll(text);
    try w.writeByte('\n');
}

/// Serializes the tree to UVL text: iterative, visited-guarded traversal
/// (a feature can be cross-listed under more than one parent), excluding
/// real OR/XOR group members from the mandatory/optional listings since
/// the group block renders them instead.
pub fn serializeHierarchy(alloc: Allocator, w: *std.Io.Writer, root_name: []const u8, hierarchy: *const std.StringHashMap(HInfo)) !void {
    try w.writeAll("features\n");

    var visited = std.StringHashMap(void).init(alloc);
    var stack = std.ArrayList(SerFrame).empty;
    try stack.append(alloc, .{ .node = .{ .name = root_name, .indent = 1 } });

    while (stack.pop()) |frame| {
        switch (frame) {
            .text => |t| try writeIndentLine(w, t.indent, t.text),
            .node => |n| {
                try writeIndentLine(w, n.indent, n.name);
                if (visited.contains(n.name)) continue;
                try visited.put(n.name, {});

                const info = hierarchy.get(n.name) orelse HInfo{};

                var group_members = std.StringHashMap(void).init(alloc);
                var real_groups = std.ArrayList(*GroupEntry).empty;
                for (info.groups.items) |g| {
                    if (g.kind != .or_group and g.kind != .xor_group) continue;
                    try real_groups.append(alloc, g);
                    for (g.members.items) |m| try group_members.put(m, {});
                }

                var mandatory = std.ArrayList([]const u8).empty;
                var optional = std.ArrayList([]const u8).empty;
                for (info.children.items) |c| {
                    if (group_members.contains(c.name)) continue;
                    if (c.kind == .mandatory) {
                        try mandatory.append(alloc, c.name);
                    } else {
                        try optional.append(alloc, c.name);
                    }
                }

                var gi = real_groups.items.len;
                while (gi > 0) {
                    gi -= 1;
                    const g = real_groups.items[gi];
                    var mi = g.members.items.len;
                    while (mi > 0) {
                        mi -= 1;
                        try stack.append(alloc, .{ .node = .{ .name = g.members.items[mi], .indent = n.indent + 2 } });
                    }
                    const keyword: []const u8 = if (g.kind == .or_group) "or" else "alternative";
                    try stack.append(alloc, .{ .text = .{ .indent = n.indent + 1, .text = keyword } });
                }
                if (optional.items.len > 0) {
                    var oi = optional.items.len;
                    while (oi > 0) {
                        oi -= 1;
                        try stack.append(alloc, .{ .node = .{ .name = optional.items[oi], .indent = n.indent + 2 } });
                    }
                    try stack.append(alloc, .{ .text = .{ .indent = n.indent + 1, .text = "optional" } });
                }
                if (mandatory.items.len > 0) {
                    var mi = mandatory.items.len;
                    while (mi > 0) {
                        mi -= 1;
                        try stack.append(alloc, .{ .node = .{ .name = mandatory.items[mi], .indent = n.indent + 2 } });
                    }
                    try stack.append(alloc, .{ .text = .{ .indent = n.indent + 1, .text = "mandatory" } });
                }
            },
        }
    }
}

/// Writes the residual-CTC constraints block: 2-literal implication
/// clauses [-child, parent] are grouped by child into
/// `child => p1 & p2 & ...`, everything else dumped as a `!x | y | z`
/// disjunction. Returns the number of constraint lines emitted.
pub fn writeResidualCtcs(alloc: Allocator, w: *std.Io.Writer, ctc_clauses: []const []const i32, id_to_name: *const std.AutoHashMap(i32, []const u8)) !usize {
    if (ctc_clauses.len == 0) return 0;
    try w.writeAll("\n\nconstraints\n");

    var implications = std.AutoHashMap(i32, std.ArrayList(i32)).init(alloc);
    var other = std.ArrayList([]const i32).empty;

    for (ctc_clauses) |c| {
        var negs: usize = 0;
        var pos: usize = 0;
        var neg_val: i32 = 0;
        var pos_val: i32 = 0;
        for (c) |lit| {
            if (lit < 0) {
                negs += 1;
                neg_val = lit;
            } else {
                pos += 1;
                pos_val = lit;
            }
        }
        if (negs == 1 and pos == 1) {
            const l = try getOrPutList(&implications, -neg_val);
            try l.append(alloc, pos_val);
        } else {
            try other.append(alloc, c);
        }
    }

    var count: usize = 0;
    var it = implications.iterator();
    while (it.next()) |entry| {
        count += 1;
        try w.print("    {s} => ", .{id_to_name.get(entry.key_ptr.*).?});
        for (entry.value_ptr.items, 0..) |p, i| {
            if (i > 0) try w.writeAll(" & ");
            try w.writeAll(id_to_name.get(p).?);
        }
        try w.writeByte('\n');
    }
    for (other.items) |c| {
        count += 1;
        try w.writeAll("    ");
        for (c, 0..) |lit, i| {
            if (i > 0) try w.writeAll(" | ");
            if (lit < 0) {
                try w.writeByte('!');
                try w.writeAll(id_to_name.get(-lit).?);
            } else {
                try w.writeAll(id_to_name.get(lit).?);
            }
        }
        try w.writeByte('\n');
    }

    return count;
}

// ---------------------------------------------------------------------------
// Residual-CTC clause computation (hierarchy vs. original CNF)
// ---------------------------------------------------------------------------

fn computeHierClauses(alloc: Allocator, hierarchy: *const std.StringHashMap(HInfo), root_name: []const u8, name_to_id: *const std.StringHashMap(i32)) !std.ArrayList([]i32) {
    var hier_clauses = std.ArrayList([]i32).empty;
    const root_id = name_to_id.get(root_name).?;
    const root_clause = try alloc.alloc(i32, 1);
    root_clause[0] = root_id;
    try hier_clauses.append(alloc, root_clause);
    try cnf.hierarchyToCnf(alloc, hierarchy, name_to_id, &hier_clauses);
    return hier_clauses;
}

fn buildClauseSet(alloc: Allocator, clauses: []const []i32) !ClauseSet {
    var set = ClauseSet.init(alloc);
    for (clauses) |c| {
        const sorted = try alloc.dupe(i32, c);
        sortByAbs(sorted);
        try set.put(sorted, {});
    }
    return set;
}

// ---------------------------------------------------------------------------
// Optimizer (greedy, incremental CTC-reduction pass)
// ---------------------------------------------------------------------------

const ClauseKind = union(enum) { impl: i32, other: void };

fn ownClausesFor(alloc: Allocator, feature_id: i32, info: *const HInfo, name_to_id: *const std.StringHashMap(i32)) !ClauseSet {
    var result = ClauseSet.init(alloc);

    for (info.children.items) |c| {
        const child_id = name_to_id.get(c.name).?;
        const pair = try alloc.alloc(i32, 2);
        pair[0] = -child_id;
        pair[1] = feature_id;
        sortByAbs(pair);
        try result.put(pair, {});
        if (c.kind == .mandatory) {
            const pair2 = try alloc.alloc(i32, 2);
            pair2[0] = -feature_id;
            pair2[1] = child_id;
            sortByAbs(pair2);
            try result.put(pair2, {});
        }
    }

    for (info.groups.items) |g| {
        if (g.kind != .or_group and g.kind != .xor_group) continue;
        const member_ids = try alloc.alloc(i32, g.members.items.len);
        for (g.members.items, 0..) |m, i| member_ids[i] = name_to_id.get(m).?;

        const clause = try alloc.alloc(i32, member_ids.len + 1);
        clause[0] = -feature_id;
        @memcpy(clause[1..], member_ids);
        sortByAbs(clause);
        try result.put(clause, {});

        if (g.kind == .xor_group) {
            var i: usize = 0;
            while (i < member_ids.len) : (i += 1) {
                var j = i + 1;
                while (j < member_ids.len) : (j += 1) {
                    const pair = try alloc.alloc(i32, 2);
                    pair[0] = -member_ids[i];
                    pair[1] = -member_ids[j];
                    sortByAbs(pair);
                    try result.put(pair, {});
                }
            }
        }
    }

    return result;
}

fn cloneHInfo(alloc: Allocator, info: HInfo) !HInfo {
    var out = HInfo{ .parent = info.parent };
    for (info.children.items) |c| try out.children.append(alloc, c);
    for (info.groups.items) |g| {
        const ng = try alloc.create(GroupEntry);
        ng.* = .{ .kind = g.kind };
        for (g.members.items) |m| try ng.members.append(alloc, m);
        try out.groups.append(alloc, ng);
    }
    return out;
}

const OptimizerState = struct {
    alloc: Allocator,
    hierarchy: *std.StringHashMap(HInfo),
    name_to_id: *const std.StringHashMap(i32),
    id_to_name: *const std.AutoHashMap(i32, []const u8),
    orig_set: *const ClauseSet,
    clause_kind: std.HashMap([]const i32, ClauseKind, ClauseSetContext, std.hash_map.default_max_load_percentage),
    contributed: std.StringHashMap(ClauseSet),
    child_counts: std.AutoHashMap(i32, i32),
    other_count: i32 = 0,
    hier_set: ClauseSet,
    depths: std.StringHashMap(i32),
    applied: usize = 0,

    fn adjustCtcCounts(self: *OptimizerState, clauses: []const []const i32, sign: i32) void {
        for (clauses) |c| {
            const kind = self.clause_kind.get(c) orelse continue;
            switch (kind) {
                .impl => |cid| {
                    const n = (self.child_counts.get(cid) orelse 0) + sign;
                    if (n <= 0) {
                        _ = self.child_counts.remove(cid);
                    } else {
                        self.child_counts.put(cid, n) catch {};
                    }
                },
                .other => self.other_count += sign,
            }
        }
    }

    fn applyClauseDelta(self: *OptimizerState, removed: []const []const i32, added: []const []const i32) !void {
        for (removed) |c| _ = self.hier_set.remove(c);
        for (added) |c| try self.hier_set.put(c, {});
        self.adjustCtcCounts(removed, 1);
        self.adjustCtcCounts(added, -1);
    }

    fn inOrigSet(self: *OptimizerState, a: i32, b: i32) bool {
        var pair = [2]i32{ a, b };
        sortByAbs(&pair);
        return self.orig_set.contains(&pair);
    }

    /// Moves child_name under new_parent_name. collectCandidates already
    /// guarantees the child isn't a real OR/XOR group member and the new
    /// parent has no real groups, so old/new group membership here never
    /// needs anything beyond a plain drop.
    fn applySingleMove(self: *OptimizerState, child_name: []const u8, new_parent_name: []const u8) !void {
        const child_id = self.name_to_id.get(child_name).?;
        const new_parent_id = self.name_to_id.get(new_parent_name).?;

        const child_info = self.hierarchy.getPtr(child_name).?;
        if (child_info.parent) |old_parent| {
            if (self.hierarchy.getPtr(old_parent)) |old_info| {
                var new_children = std.ArrayList(ChildEdge).empty;
                for (old_info.children.items) |c| {
                    if (!std.mem.eql(u8, c.name, child_name)) try new_children.append(self.alloc, c);
                }
                old_info.children = new_children;

                var new_groups = std.ArrayList(*GroupEntry).empty;
                for (old_info.groups.items) |g| {
                    if (!containsStr(g.members.items, child_name)) try new_groups.append(self.alloc, g);
                }
                old_info.groups = new_groups;
            }
        }

        const new_info = self.hierarchy.getPtr(new_parent_name).?;

        var seen = std.StringHashMap(void).init(self.alloc);
        for (new_info.children.items) |c| try seen.put(c.name, {});
        for (new_info.groups.items) |g| {
            for (g.members.items) |m| {
                if (!seen.contains(m)) {
                    try seen.put(m, {});
                    try new_info.children.append(self.alloc, .{ .name = m, .kind = .optional });
                }
            }
        }
        new_info.groups.clearRetainingCapacity();

        for (new_info.children.items) |*c| {
            if (self.inOrigSet(-new_parent_id, self.name_to_id.get(c.name).?)) {
                c.kind = .mandatory;
            }
        }

        const rel: ChildType = if (self.inOrigSet(-new_parent_id, child_id)) .mandatory else .optional;
        child_info.parent = new_parent_name;
        try new_info.children.append(self.alloc, .{ .name = child_name, .kind = rel });
    }
};

fn containsStr(haystack: []const []const u8, needle: []const u8) bool {
    for (haystack) |s| {
        if (std.mem.eql(u8, s, needle)) return true;
    }
    return false;
}

/// True if child_name is an ancestor of new_parent_name (moving child_name
/// under new_parent_name would create a cycle).
fn wouldCycle(hierarchy: *const std.StringHashMap(HInfo), new_parent_name: []const u8, child_name: []const u8) bool {
    var ancestor: ?[]const u8 = new_parent_name;
    var guard: usize = 0;
    while (ancestor) |anc| {
        guard += 1;
        if (guard > 1_000_000) return false; // defensive: shouldn't happen on a real tree
        if (std.mem.eql(u8, anc, child_name)) return true;
        const anc_info = hierarchy.get(anc) orelse return false;
        ancestor = anc_info.parent;
    }
    return false;
}

const Candidate = struct { child: []const u8, parent: []const u8, depth: i32 };

/// Collects move candidates: 2-literal CTCs [-A, B] not already covered by
/// the hierarchy become "try moving A under B", filtered to skip mandatory
/// pairs, moves landing under a parent with real OR/XOR groups, moves of a
/// real group member out of its group, cycles, and non-upward moves.
/// Keeps only the shallowest valid new parent per child.
fn collectCandidates(alloc: Allocator, state: *OptimizerState, orig_clauses: []const []i32) !std.StringHashMap(Candidate) {
    var raw = std.StringHashMap(Candidate).init(alloc);

    for (orig_clauses) |clause| {
        if (clause.len != 2) continue;
        var negs: usize = 0;
        var pos: usize = 0;
        var a: i32 = 0;
        var b: i32 = 0;
        for (clause) |lit| {
            if (lit < 0) {
                negs += 1;
                a = lit;
            } else {
                pos += 1;
                b = lit;
            }
        }
        if (negs != 1 or pos != 1) continue;
        if (state.hier_set.contains(clause)) continue;

        const child_name = state.id_to_name.get(-a) orelse continue;
        const parent_name = state.id_to_name.get(b) orelse continue;

        const child_info = state.hierarchy.get(child_name) orelse continue;
        const parent_info = state.hierarchy.get(parent_name) orelse continue;

        if (child_info.parent) |cp| {
            if (std.mem.eql(u8, cp, parent_name)) continue;
        }

        var parent_has_real_group = false;
        for (parent_info.groups.items) |g| {
            if (g.kind == .or_group or g.kind == .xor_group) {
                parent_has_real_group = true;
                break;
            }
        }
        if (parent_has_real_group) continue;

        if (child_info.parent) |old_parent_name| {
            if (state.hierarchy.get(old_parent_name)) |old_info| {
                var in_real_group = false;
                for (old_info.groups.items) |g| {
                    if ((g.kind == .or_group or g.kind == .xor_group) and containsStr(g.members.items, child_name)) {
                        in_real_group = true;
                        break;
                    }
                }
                if (in_real_group) continue;
            }
        }

        if (wouldCycle(state.hierarchy, parent_name, child_name)) continue;

        const d = state.depths.get(parent_name) orelse 9999;
        const gop = try raw.getOrPut(child_name);
        if (!gop.found_existing or d < gop.value_ptr.depth) {
            gop.value_ptr.* = .{ .child = child_name, .parent = parent_name, .depth = d };
        }
    }

    return raw;
}

/// Greedy CTC-reduction pass. Candidates are batched by new parent
/// (largest batch first), each batch applied speculatively and rolled
/// back unless it provably doesn't increase the residual CTC count,
/// tracked via incremental per-feature clause-contribution deltas instead
/// of recomputing the whole tree's CNF per batch.
pub fn runOptimizer(alloc: Allocator, hierarchy: *std.StringHashMap(HInfo), root_name: []const u8, name_to_id: *const std.StringHashMap(i32), id_to_name: *const std.AutoHashMap(i32, []const u8), orig_clauses: []const []i32, orig_set: *const ClauseSet, hier_set: *ClauseSet) !usize {
    var depths = std.StringHashMap(i32).init(alloc);
    {
        try depths.put(root_name, 0);
        var queue = std.ArrayList([]const u8).empty;
        try queue.append(alloc, root_name);
        var qi: usize = 0;
        while (qi < queue.items.len) : (qi += 1) {
            const f = queue.items[qi];
            const d = depths.get(f).?;
            const info = hierarchy.get(f) orelse continue;
            for (info.children.items) |c| {
                if (!depths.contains(c.name)) {
                    try depths.put(c.name, d + 1);
                    try queue.append(alloc, c.name);
                }
            }
        }
    }

    var clause_kind = std.HashMap([]const i32, ClauseKind, ClauseSetContext, std.hash_map.default_max_load_percentage).init(alloc);
    {
        var it = orig_set.keyIterator();
        while (it.next()) |c| {
            var negs: usize = 0;
            var pos: usize = 0;
            var neg_val: i32 = 0;
            for (c.*) |lit| {
                if (lit < 0) {
                    negs += 1;
                    neg_val = lit;
                } else pos += 1;
            }
            if (negs == 1 and pos == 1) {
                try clause_kind.put(c.*, .{ .impl = -neg_val });
            } else {
                try clause_kind.put(c.*, .other);
            }
        }
    }

    var contributed = std.StringHashMap(ClauseSet).init(alloc);
    {
        var it = hierarchy.iterator();
        while (it.next()) |entry| {
            const fid = name_to_id.get(entry.key_ptr.*).?;
            try contributed.put(entry.key_ptr.*, try ownClausesFor(alloc, fid, entry.value_ptr, name_to_id));
        }
    }

    var child_counts = std.AutoHashMap(i32, i32).init(alloc);
    var other_count: i32 = 0;
    {
        var it = orig_set.keyIterator();
        while (it.next()) |c| {
            if (hier_set.contains(c.*)) continue;
            const kind = clause_kind.get(c.*).?;
            switch (kind) {
                .impl => |cid| {
                    const n = (child_counts.get(cid) orelse 0) + 1;
                    try child_counts.put(cid, n);
                },
                .other => other_count += 1,
            }
        }
    }

    var state = OptimizerState{
        .alloc = alloc,
        .hierarchy = hierarchy,
        .name_to_id = name_to_id,
        .id_to_name = id_to_name,
        .orig_set = orig_set,
        .clause_kind = clause_kind,
        .contributed = contributed,
        .child_counts = child_counts,
        .other_count = other_count,
        .hier_set = hier_set.*,
        .depths = depths,
    };

    const raw_candidates = try collectCandidates(alloc, &state, orig_clauses);

    var groups_by_parent = std.StringHashMap(std.ArrayList([]const u8)).init(alloc);
    {
        var it = raw_candidates.iterator();
        while (it.next()) |entry| {
            const cand = entry.value_ptr.*;
            const gop = try groups_by_parent.getOrPut(cand.parent);
            if (!gop.found_existing) gop.value_ptr.* = std.ArrayList([]const u8).empty;
            try gop.value_ptr.append(alloc, cand.child);
        }
    }

    const BatchEntry = struct { parent: []const u8, children: []const []const u8 };
    var batches = std.ArrayList(BatchEntry).empty;
    {
        var it = groups_by_parent.iterator();
        while (it.next()) |entry| {
            try batches.append(alloc, .{ .parent = entry.key_ptr.*, .children = entry.value_ptr.items });
        }
    }
    std.mem.sort(BatchEntry, batches.items, {}, struct {
        fn lessThan(_: void, a: BatchEntry, b: BatchEntry) bool {
            return a.children.len > b.children.len; // largest batch first
        }
    }.lessThan);

    var current_ctcs: i32 = @as(i32, @intCast(state.child_counts.count())) + state.other_count;

    for (batches.items) |batch| {
        const ctcs_before = current_ctcs;

        var touched = std.StringHashMap(void).init(alloc);
        try touched.put(batch.parent, {});
        for (batch.children) |child_name| {
            try touched.put(child_name, {});
            if (hierarchy.get(child_name)) |info| {
                if (info.parent) |op| try touched.put(op, {});
            }
        }

        var snapshot = std.StringHashMap(HInfo).init(alloc);
        var before_contrib = std.StringHashMap(ClauseSet).init(alloc);
        {
            var tit = touched.keyIterator();
            while (tit.next()) |name| {
                if (hierarchy.get(name.*)) |info| {
                    try snapshot.put(name.*, try cloneHInfo(alloc, info));
                }
                try before_contrib.put(name.*, state.contributed.get(name.*) orelse ClauseSet.init(alloc));
            }
        }

        var moved = std.ArrayList([]const u8).empty;
        for (batch.children) |child_name| {
            if (wouldCycle(hierarchy, batch.parent, child_name)) continue;

            const cur_parent = (hierarchy.get(child_name) orelse continue).parent;
            if (cur_parent) |cp| {
                if (std.mem.eql(u8, cp, batch.parent)) continue;
            }

            try state.applySingleMove(child_name, batch.parent);
            try moved.append(alloc, child_name);
        }

        if (moved.items.len == 0) continue;

        var after_contrib = std.StringHashMap(ClauseSet).init(alloc);
        {
            var tit = touched.keyIterator();
            while (tit.next()) |name| {
                if (hierarchy.get(name.*)) |info| {
                    const fid = name_to_id.get(name.*).?;
                    try after_contrib.put(name.*, try ownClausesFor(alloc, fid, &info, name_to_id));
                } else {
                    try after_contrib.put(name.*, ClauseSet.init(alloc));
                }
            }
        }

        var all_removed = std.ArrayList([]const i32).empty;
        var all_added = std.ArrayList([]const i32).empty;
        {
            var tit = touched.keyIterator();
            while (tit.next()) |name| {
                const old_c = before_contrib.get(name.*).?;
                const new_c = after_contrib.get(name.*).?;
                var oit = old_c.keyIterator();
                while (oit.next()) |c| {
                    if (!new_c.contains(c.*)) try all_removed.append(alloc, c.*);
                }
                var nit = new_c.keyIterator();
                while (nit.next()) |c| {
                    if (!old_c.contains(c.*)) try all_added.append(alloc, c.*);
                }
            }
        }

        try state.applyClauseDelta(all_removed.items, all_added.items);

        var subset_ok = true;
        for (all_added.items) |c| {
            if (!state.clause_kind.contains(c)) {
                subset_ok = false;
                break;
            }
        }
        const ctcs_after: i32 = @as(i32, @intCast(state.child_counts.count())) + state.other_count;
        const reject = !subset_ok or (moved.items.len >= 2 and ctcs_after > ctcs_before) or (moved.items.len == 1 and ctcs_after >= ctcs_before);

        if (reject) {
            try state.applyClauseDelta(all_added.items, all_removed.items); // reverse
            var sit = snapshot.iterator();
            while (sit.next()) |entry| {
                try hierarchy.put(entry.key_ptr.*, entry.value_ptr.*);
            }
            continue;
        }

        state.applied += moved.items.len;
        current_ctcs = ctcs_after;
        var tit2 = touched.keyIterator();
        while (tit2.next()) |name| {
            if (after_contrib.get(name.*)) |c| try state.contributed.put(name.*, c);
        }
    }

    hier_set.* = state.hier_set;
    return state.applied;
}

// ---------------------------------------------------------------------------
// Top-level entry point
// ---------------------------------------------------------------------------

pub const RecoverError = error{NoRoot} || Allocator.Error;

/// scratch_alloc is used for intermediate work (freed by the caller
/// tearing down its arena); out_alloc allocates the returned UVL text so
/// it survives that teardown. `infer_propagation` gates the experimental
/// Level 2 propagation-based implication recovery (see the section doc
/// comment above `augmentGraphWithPropagation`); off by default.
pub fn recover(scratch_alloc: Allocator, out_alloc: Allocator, dimacs: []const u8, optimize: bool, by_name: bool, infer_propagation: bool) ![]const u8 {
    const parsed = try parseDimacs(scratch_alloc, dimacs);
    return recoverFromParsed(scratch_alloc, out_alloc, parsed, optimize, by_name, infer_propagation, &.{});
}

/// Core of `recover()`, taking an already-parsed clause set instead of
/// raw DIMACS text -- lets any front end that can produce a `ParsedDimacs`
/// shape (feature ids/names + `[]const i32` clauses) reuse the entire
/// hierarchy-recovery pipeline below unchanged. Used by `recover()` itself
/// (DIMACS) and by `smtlib.recoverFromSmt` (SMT-LIB 2), which flattens the
/// input's Boolean-only asserts into clauses the same way and passes
/// anything it can't flatten (an Int/String/`ite`-involving assert) as
/// `extra_constraints` -- raw UVL constraint-syntax text lines appended to
/// the output verbatim, after the CNF-derived residual CTCs, the same
/// "never silently drop it" policy `uvl2uvl` uses for content it can't
/// judge.
pub fn recoverFromParsed(
    scratch_alloc: Allocator,
    out_alloc: Allocator,
    parsed: ParsedDimacs,
    optimize: bool,
    by_name: bool,
    infer_propagation: bool,
    extra_constraints: []const []const u8,
) ![]const u8 {
    const alloc = scratch_alloc;
    var graph = try buildGraph(alloc, parsed.clauses.items);
    if (infer_propagation) {
        var max_id: i32 = 0;
        var it = parsed.id_to_name.keyIterator();
        while (it.next()) |k| {
            if (k.* > max_id) max_id = k.*;
        }
        try augmentGraphWithPropagation(alloc, &graph, parsed.clauses.items, max_id);
    }

    // A unit clause can be negative ("this feature must be unselected"),
    // which isn't a root candidate: there's no feature id to attach to
    // the tree for it. It surfaces as a residual `!Feature` constraint
    // instead, same as any other clause the hierarchy doesn't cover.
    var root_candidates = std.ArrayList(i32).empty;
    for (parsed.clauses.items) |c| {
        if (c.len == 1 and c[0] > 0) try root_candidates.append(alloc, c[0]);
    }
    if (root_candidates.items.len == 0) return RecoverError.NoRoot;
    const root = root_candidates.items[0];

    const fd = try findDepths(alloc, root, &graph, &parsed.id_to_name, by_name);
    var parents = fd.parents;
    for (root_candidates.items[1..]) |extra| {
        if (extra != root and !parents.contains(extra)) {
            try parents.put(extra, .{ .parent = root, .kind = .mandatory });
        }
    }

    var parents2childs = std.AutoHashMap(i32, std.ArrayList(ChildRef)).init(alloc);
    {
        var it = parents.iterator();
        while (it.next()) |e| {
            if (e.value_ptr.kind == .group) continue;
            const gop = try parents2childs.getOrPut(e.value_ptr.parent);
            if (!gop.found_existing) gop.value_ptr.* = std.ArrayList(ChildRef).empty;
            try gop.value_ptr.append(alloc, .{ .id = e.key_ptr.*, .mandatory = e.value_ptr.kind == .mandatory });
        }
    }

    var clause_set = try buildClauseSet(alloc, parsed.clauses.items);

    var built = try buildHierarchy(alloc, root, &parents2childs, &graph.groups, &parsed.id_to_name, &clause_set);

    const hier_clauses = try computeHierClauses(alloc, &built.hierarchy, built.root_name, &parsed.name_to_id);
    var hier_set = try buildClauseSet(alloc, hier_clauses.items);

    if (optimize) {
        const applied = try runOptimizer(alloc, &built.hierarchy, built.root_name, &parsed.name_to_id, &parsed.id_to_name, parsed.clauses.items, &clause_set, &hier_set);
        std.debug.print("optimize_from_cnf: {d} moves applied\n", .{applied});
    }

    var aw = std.Io.Writer.Allocating.init(out_alloc);
    defer aw.deinit();
    try serializeHierarchy(alloc, &aw.writer, built.root_name, &built.hierarchy);

    var ctc_clauses = std.ArrayList([]const i32).empty;
    for (parsed.clauses.items) |c| {
        if (!hier_set.contains(c)) try ctc_clauses.append(alloc, c);
    }
    // With --optimize, the greedy re-parenting pass leaves whatever residual
    // CTCs it couldn't absorb into the tree, but never itself removes a CTC
    // that a *different* CTC already subsumes (that's an orthogonal
    // simplification, not a re-parenting move). Running the same
    // equivalence-preserving global subsumption pass used elsewhere in the
    // pipeline (see docs/pipeline_clause_dedup.md) over just this residual
    // set cleans that up. Safe without a satisfiability check: ctc_clauses
    // is a subset of the original (necessarily satisfiable) parsed.clauses,
    // so it can never turn out UNSAT on its own. Baseline (non-optimized)
    // output is left as-is, matching its existing "literal residual" contract.
    if (optimize) {
        const simplified = try subsumption.simplify(alloc, ctc_clauses.items, false);
        ctc_clauses = std.ArrayList([]const i32).empty;
        for (simplified.clauses) |c| try ctc_clauses.append(alloc, c);
    }
    const n_ctcs = try writeResidualCtcs(alloc, &aw.writer, ctc_clauses.items, &parsed.id_to_name);
    if (optimize) {
        std.debug.print("optimize_from_cnf: {d} CTCs remaining\n", .{n_ctcs});
    }

    if (extra_constraints.len > 0) {
        // writeResidualCtcs only opens the "constraints" block itself
        // when it has clauses of its own to write.
        if (n_ctcs == 0) try aw.writer.writeAll("\n\nconstraints\n");
        for (extra_constraints) |c| {
            try aw.writer.writeAll("    ");
            try aw.writer.writeAll(c);
            try aw.writer.writeByte('\n');
        }
    }

    return try aw.toOwnedSlice();
}

pub const VerifyResult = struct {
    total_orig_clauses: usize,
    missing: usize,
    extra: usize,

    pub fn pass(self: VerifyResult) bool {
        return self.missing == 0 and self.extra == 0;
    }
};

/// Re-parses `uvl_text` and compares its CNF against `orig_clauses` as an
/// exact clause set -- DIMACS input only. Returns counts rather than
/// printing, so the result is directly assertable in a test or usable by
/// a ctypes caller; a false FAIL (missing=N, extra=0) is possible after
/// `--optimize`'s subsumption cleanup -- see any2uvl.zig's usage() text.
pub fn verifyRecovery(alloc: Allocator, uvl_text: []const u8, orig_clauses: []const []i32) !VerifyResult {
    const tokens = try lexer.tokenize(alloc, uvl_text);
    const result = try parser_mod.parseModel(alloc, tokens);
    var ids = try cnf.assignIds(alloc, &result.builder.features);

    var clauses = std.ArrayList([]i32).empty;
    if (result.builder.root) |root| {
        const clause = try alloc.alloc(i32, 1);
        clause[0] = ids.get(root).?;
        try clauses.append(alloc, clause);
    }
    try cnf.hierarchyToCnf(alloc, &result.builder.hierarchy, &ids, &clauses);

    for (result.constraints) |info| {
        const node = info.node orelse continue;
        const node_clauses = constraint.generateClauses(alloc, &ids, node) catch continue;
        for (node_clauses) |c| try clauses.append(alloc, c);
    }

    var orig_set = std.HashMap([]i32, void, SortedClauseCtx, std.hash_map.default_max_load_percentage).init(alloc);
    for (orig_clauses) |c| try orig_set.put(try sortedCopy(alloc, c), {});

    var result_set = std.HashMap([]i32, void, SortedClauseCtx, std.hash_map.default_max_load_percentage).init(alloc);
    for (clauses.items) |c| try result_set.put(try sortedCopy(alloc, c), {});

    var missing: usize = 0;
    var it = orig_set.keyIterator();
    while (it.next()) |k| {
        if (!result_set.contains(k.*)) missing += 1;
    }
    var extra: usize = 0;
    var it2 = result_set.keyIterator();
    while (it2.next()) |k| {
        if (!orig_set.contains(k.*)) extra += 1;
    }

    return .{ .total_orig_clauses = orig_set.count(), .missing = missing, .extra = extra };
}

fn sortedCopy(alloc: Allocator, c: []const i32) ![]i32 {
    const copy = try alloc.dupe(i32, c);
    std.mem.sort(i32, copy, {}, std.sort.asc(i32));
    return copy;
}

const SortedClauseCtx = struct {
    pub fn hash(_: SortedClauseCtx, key: []i32) u64 {
        return std.hash.Wyhash.hash(0, std.mem.sliceAsBytes(key));
    }
    pub fn eql(_: SortedClauseCtx, a: []i32, b: []i32) bool {
        return std.mem.eql(i32, a, b);
    }
};

test "ratio matches difflib for identical strings" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    try std.testing.expectApproxEqAbs(@as(f64, 1.0), try ratio(alloc, "abc", "abc"), 1e-9);
}

test "ratio matches difflib for abc vs abd" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    // difflib.SequenceMatcher(None, "abc", "abd").ratio() == 0.6666666666666666
    try std.testing.expectApproxEqAbs(@as(f64, 2.0 / 3.0), try ratio(alloc, "abc", "abd"), 1e-9);
}

test "ratio matches difflib for disjoint strings" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    try std.testing.expectApproxEqAbs(@as(f64, 0.0), try ratio(alloc, "abc", "xyz"), 1e-9);
}

test "ratio matches difflib for realistic feature-name pairs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    try std.testing.expectApproxEqAbs(@as(f64, 0.8333333333333334), try ratio(alloc, "BTreeCache", "BTreeCacheSize"), 1e-9);
    try std.testing.expectApproxEqAbs(@as(f64, 0.45454545454545453), try ratio(alloc, "CacheSize", "LogBufferSize"), 1e-9);
}

test "group detection rejects ambiguous multi-parent member sets" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Root(1) -> A(2), B(3), C(4) as a real xor group under Root: clauses
    // [-2,1] [-3,1] [-4,1] [-1,2,3,4] [-2,-3] [-2,-4] [-3,-4] [1]
    var clauses = std.ArrayList([]i32).empty;
    const c1 = try alloc.dupe(i32, &[_]i32{ -2, 1 });
    const c2 = try alloc.dupe(i32, &[_]i32{ -3, 1 });
    const c3 = try alloc.dupe(i32, &[_]i32{ -4, 1 });
    const c4 = try alloc.dupe(i32, &[_]i32{ -1, 2, 3, 4 });
    sortByAbs(c4);
    try clauses.append(alloc, c1);
    try clauses.append(alloc, c2);
    try clauses.append(alloc, c3);
    try clauses.append(alloc, c4);

    const graph = try buildGraph(alloc, clauses.items);
    try std.testing.expect(graph.groups.contains(1));
    const members = graph.groups.get(1).?;
    try std.testing.expectEqual(@as(usize, 3), members.items.len);
}

test "Level 2: propagation recovers a multi-clause implication with no literal 2-clause edge" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Root(3) unit true. A(1)=>Root, B(4)=>Root, C(2)=>Root (structural).
    // B => not C: {-4,-2}. B => (A or C): {-4,1,2}.
    // Together: B=>A, with NO literal clause {-4,1} anywhere.
    var clauses = std.ArrayList([]i32).empty;
    const c1 = try alloc.dupe(i32, &[_]i32{3});
    const c2 = try alloc.dupe(i32, &[_]i32{ -1, 3 });
    const c3 = try alloc.dupe(i32, &[_]i32{ -4, 3 });
    const c4 = try alloc.dupe(i32, &[_]i32{ -2, 3 });
    const c5 = try alloc.dupe(i32, &[_]i32{ -4, -2 });
    const c6 = try alloc.dupe(i32, &[_]i32{ -4, 1, 2 });
    sortByAbs(c6);
    try clauses.append(alloc, c1);
    try clauses.append(alloc, c2);
    try clauses.append(alloc, c3);
    try clauses.append(alloc, c4);
    try clauses.append(alloc, c5);
    try clauses.append(alloc, c6);

    var graph = try buildGraph(alloc, clauses.items);
    // Before Level 2: B(4) has no edge to A(1).
    if (graph.implies.get(4)) |l| {
        try std.testing.expect(!containsI32(l.items, 1));
    }

    try augmentGraphWithPropagation(alloc, &graph, clauses.items, 4);

    const implies4 = graph.implies.get(4) orelse return error.TestUnexpectedResult;
    try std.testing.expect(containsI32(implies4.items, 1));
}

test "parseDimacs rejects input with no `p` header line (e.g. non-DIMACS)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    try std.testing.expectError(ParseDimacsError.NoHeader, parseDimacs(alloc, "1 2 0\n-1 0\n"));
}

test "parseDimacs accepts a header-only, clause-only DIMACS file" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseDimacs(alloc, "p cnf 1 1\n1 0\n");
    try std.testing.expectEqual(@as(usize, 1), parsed.clauses.items.len);
}

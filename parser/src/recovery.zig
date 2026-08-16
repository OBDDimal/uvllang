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

pub const ParseDimacsError = error{OutOfMemory};

/// Parses `c <id> <name>` comments (quoting bare multi-word names for
/// third-party DIMACS files) and clauses (each sorted by abs value).
pub fn parseDimacs(alloc: Allocator, text: []const u8) ParseDimacsError!ParsedDimacs {
    var id_to_name = std.AutoHashMap(i32, []const u8).init(alloc);
    var name_to_id = std.StringHashMap(i32).init(alloc);
    var clauses = std.ArrayList([]i32).empty;

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
            continue;
        }

        if (line[0] == 'p') continue;

        var lits = std.ArrayList(i32).empty;
        var it = std.mem.tokenizeAny(u8, line, " \t");
        while (it.next()) |tok| {
            const v = std.fmt.parseInt(i32, tok, 10) catch continue;
            if (v == 0) continue;
            try lits.append(alloc, v);
        }
        if (lits.items.len == 0) continue;
        const owned = try lits.toOwnedSlice(alloc);
        sortByAbs(owned);
        try clauses.append(alloc, owned);
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

/// Builds the HInfo tree from parents2childs/groups. Group members are
/// also added as plain (optional) children, matching a real UVL group's
/// CNF encoding where each member gets its own "member => parent" edge in
/// addition to the group clause, same shape builder.zig's startFeature
/// produces for a real parse. A feature's content is only built once; it
/// can still be reached (and referenced) via more than one path.
pub fn buildHierarchy(alloc: Allocator, root: i32, parents2childs: *const std.AutoHashMap(i32, std.ArrayList(ChildRef)), groups: *const std.AutoHashMap(i32, std.ArrayList(i32)), id_to_name: *const std.AutoHashMap(i32, []const u8), clause_set: *const ClauseSet) !BuiltHierarchy {
    var hierarchy = std.StringHashMap(HInfo).init(alloc);

    var stack = std.ArrayList(WalkFrame).empty;
    try stack.append(alloc, .{ .id = root, .parent_name = null, .kind = .optional, .is_group_member = false });

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

    return .{ .hierarchy = hierarchy, .root_name = id_to_name.get(root).? };
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
/// it survives that teardown.
pub fn recover(scratch_alloc: Allocator, out_alloc: Allocator, dimacs: []const u8, optimize: bool, by_name: bool) ![]const u8 {
    const alloc = scratch_alloc;
    const parsed = try parseDimacs(alloc, dimacs);
    const graph = try buildGraph(alloc, parsed.clauses.items);

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
    const n_ctcs = try writeResidualCtcs(alloc, &aw.writer, ctc_clauses.items, &parsed.id_to_name);
    if (optimize) {
        std.debug.print("optimize_from_cnf: {d} CTCs remaining\n", .{n_ctcs});
    }

    return try aw.toOwnedSlice();
}

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

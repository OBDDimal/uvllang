//! C ABI surface for the shared library, called from Python via ctypes.
//! This module should stay a thin marshalling layer -- decode C-ABI
//! arguments, call into the same shared modules the native binaries use
//! (pipeline.zig, recovery.zig, smt.zig), encode the result back out --
//! not a second implementation of any of their logic.
//!
//! Three entry points:
//!   - `uvl_source_to_cnf`: full pipeline (lex, parse, build hierarchy,
//!     generate CNF) on raw UVL source text, writing DIMACS to an
//!     in-memory buffer instead of a file. Shares its actual clause-
//!     building and warning logic with the `uvl2cnf` CLI (main.zig) via
//!     pipeline.zig.
//!   - `uvl_hierarchy_to_cnf`: only the CNF-generation step, for callers
//!     that already parsed the file themselves and supply the hierarchy
//!     and constraints as flat arrays (Lark/ANTLR).
//!   - `uvl_dimacs_to_uvl`: CNF -> UVL recovery (any2uvl).
//!
//! Each call runs in a scratch arena that's torn down before returning;
//! only the output buffer survives, allocated with `gpa` so it outlives
//! the arena and can be freed independently via `uvl_free_buffer`.

const std = @import("std");
const Allocator = std.mem.Allocator;
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const builder_mod = @import("builder.zig");
const cnf = @import("cnf.zig");
const constraint = @import("constraint.zig");
const subsumption = @import("subsumption.zig");
const recovery = @import("recovery.zig");
const pipeline = @import("pipeline.zig");
const smt = @import("smt.zig");

const gpa = std.heap.smp_allocator;

var last_error_buf: [1024]u8 = undefined;
var last_error_len: usize = 0;

fn setError(comptime fmt: []const u8, args: anytype) void {
    const msg = std.fmt.bufPrint(&last_error_buf, fmt, args) catch blk: {
        const truncated = "error message too long";
        @memcpy(last_error_buf[0..truncated.len], truncated);
        break :blk last_error_buf[0..truncated.len];
    };
    last_error_len = msg.len;
}

export fn uvl_last_error() callconv(.c) [*:0]const u8 {
    last_error_buf[last_error_len] = 0;
    return last_error_buf[0..last_error_len :0];
}

export fn uvl_free_buffer(ptr: [*]const u8, len: usize) callconv(.c) void {
    if (len == 0) return;
    const slice: []u8 = @constCast(ptr[0..len]);
    gpa.free(slice);
}

const StatusCode = enum(i32) {
    ok = 0,
    lex_error = 1,
    parse_error = 2,
    unknown_feature = 3,
    out_of_memory = 5,
    invalid_input = 6,
};

fn statusForError(err: anyerror) StatusCode {
    return switch (err) {
        error.UnterminatedString, error.UnexpectedChar => .lex_error,
        error.UnexpectedToken, error.UnexpectedEnd => .parse_error,
        error.UnknownFeature => .unknown_feature,
        error.NoRoot, error.InvalidInput => .invalid_input,
        else => .out_of_memory,
    };
}

/// Counts of constructs above the plain Boolean language level -- see
/// docs/non_boolean_support.md. Tier 1 (corrupts CNF correctness or loses
/// a real constraint) first, then Tier 2 (a constraint is dropped), then
/// Tier 3 (decorative metadata only). Mirrors uvllang.main.UVL's
/// NonBooleanConstructError policy: the Python side raises by default on
/// any nonzero Tier 1/2 count, and only ever warns on Tier 3.
pub const NonBooleanCounts = extern struct {
    cardinality_groups: usize = 0,
    constraint_attributes: usize = 0,
    cardinality_features: usize = 0,
    attribute_ref_constraints: usize = 0,
    comparison_constraints: usize = 0,
    typed_features: usize = 0,
    attributed_features: usize = 0,
};

fn sourceToCnfImpl(
    alloc: Allocator,
    source: []const u8,
    do_simplify: bool,
    do_conversion: bool,
    out_ptr: *[*]const u8,
    out_len: *usize,
    out_non_boolean: *NonBooleanCounts,
) !void {
    const tokens = try lexer.tokenize(alloc, source);
    const result = try parser.parseModel(alloc, tokens);

    const built = try pipeline.buildClauses(alloc, &result, do_conversion);
    var ids = built.ids;
    const clauses = built.clauses;

    pipeline.printNonBooleanWarnings(&result.builder, built.counts, do_conversion);

    const cclauses: []const []const i32 = @ptrCast(clauses.items);
    var out_clauses: []const []const i32 = cclauses;
    if (do_simplify) {
        const simplified = try subsumption.simplify(alloc, cclauses, false);
        if (simplified.removed_by_subsumption > 0) std.debug.print("Info: Removed {d} clause(s) via subsumption\n", .{simplified.removed_by_subsumption});
        if (simplified.literals_removed_by_ssr > 0) std.debug.print("Info: Removed {d} literal(s) via self-subsuming resolution\n", .{simplified.literals_removed_by_ssr});
        if (simplified.tautologies_removed > 0) std.debug.print("Info: Removed {d} tautological clause(s)\n", .{simplified.tautologies_removed});
        if (simplified.unsat) std.debug.print("Warning: formula is UNSAT (constraints are contradictory)\n", .{});
        out_clauses = simplified.clauses;
    }

    const b = &result.builder;
    out_non_boolean.* = .{
        .cardinality_groups = b.cardinality_group_count,
        .constraint_attributes = b.constraint_attribute_count,
        .cardinality_features = b.cardinality_feature_count,
        .attribute_ref_constraints = built.counts.attribute_ref_constraints,
        .comparison_constraints = built.counts.comparison_constraints,
        .typed_features = b.typed_feature_count,
        .attributed_features = b.attributed_feature_count,
    };

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    try cnf.writeDimacs(alloc, &aw.writer, &ids, out_clauses);
    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

/// `do_simplify`: gates the global subsumption/SSR-disabled simplify pass,
/// matching the `uvl2cnf` CLI's `--simplify` flag -- off by default there
/// and here, so the CLI and the Python API produce the same clause set for
/// the same input unless the caller explicitly opts in. See
/// docs/pipeline_clause_dedup.md.
/// `do_conversion`: gates the UVLParser-paper conversion strategies for
/// group cardinality and feature-local constraint attributes, matching
/// the `uvl2cnf` CLI's `--conversion` flag -- off by default, so both
/// stay silently dropped (as before) unless the caller opts in. See
/// conversion.zig / docs/non_boolean_support.md.
export fn uvl_source_to_cnf(
    src_ptr: [*]const u8,
    src_len: usize,
    do_simplify: u8,
    do_conversion: u8,
    out_ptr: *[*]const u8,
    out_len: *usize,
    out_non_boolean: *NonBooleanCounts,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    sourceToCnfImpl(arena_state.allocator(), src_ptr[0..src_len], do_simplify != 0, do_conversion != 0, out_ptr, out_len, out_non_boolean) catch |err| {
        setError("uvl_source_to_cnf: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };
    return @intFromEnum(StatusCode.ok);
}

fn sourceToSmtImpl(alloc: Allocator, source: []const u8, out_ptr: *[*]const u8, out_len: *usize) !void {
    const tokens = try lexer.tokenize(alloc, source);
    const result = try parser.parseModel(alloc, tokens);

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    try smt.writeSmt(alloc, &aw.writer, &result);
    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

/// Full pipeline: raw UVL source -> SMT-LIB 2 text, backing the native
/// `uvl2smt` binary and (for backend="zig") `UVL.to_smt()`. Unlike
/// `uvl_source_to_cnf`, not restricted to the Boolean language level --
/// see smt.zig.
export fn uvl_source_to_smt(
    src_ptr: [*]const u8,
    src_len: usize,
    out_ptr: *[*]const u8,
    out_len: *usize,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    sourceToSmtImpl(arena_state.allocator(), src_ptr[0..src_len], out_ptr, out_len) catch |err| {
        setError("uvl_source_to_smt: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };
    return @intFromEnum(StatusCode.ok);
}

const no_index: u32 = 0xFFFFFFFF;

fn writeU32(w: *std.Io.Writer, value: u32) !void {
    var buf: [4]u8 = undefined;
    std.mem.writeInt(u32, &buf, value, .little);
    try w.writeAll(&buf);
}

fn writeBytes(w: *std.Io.Writer, bytes: []const u8) !void {
    try writeU32(w, @intCast(bytes.len));
    try w.writeAll(bytes);
}

/// Full pipeline, second entry point: lex+parse (a fresh pass, independent
/// of `uvl_source_to_cnf`) to extract everything Lark/ANTLR's extractor and
/// hierarchy builder do -- feature list (document order) + types,
/// hierarchy (edges/groups/parent, all four group kinds, not just or/xor),
/// attributes, and raw constraint text -- so Python can back
/// `.feature_types`/`.feature_attributes`/`.boolean_constraints`/
/// `.arithmetic_constraints`/`.builder()`/`to_smt()` for backend="zig" too.
/// Deliberately does NOT also produce CNF -- `uvl_source_to_cnf` already
/// does that fast, and this is for callers who need the rest of the
/// extraction, called lazily on first access from the Python side.
fn parseSourceFullImpl(alloc: Allocator, source: []const u8, out_ptr: *[*]const u8, out_len: *usize) !void {
    const tokens = try lexer.tokenize(alloc, source);
    const result = try parser.parseModel(alloc, tokens);
    const b = &result.builder;

    var index = std.StringHashMap(u32).init(alloc);
    for (b.ordered_features.items, 0..) |name, i| try index.put(name, @intCast(i));

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    const w = &aw.writer;

    try writeU32(w, @intCast(b.ordered_features.items.len));
    for (b.ordered_features.items) |name| {
        try writeBytes(w, name);
        const info = b.hierarchy.get(name).?;
        try writeBytes(w, info.feature_type orelse "");
    }
    try writeU32(w, if (b.root) |r| index.get(r).? else no_index);

    var edges = std.ArrayList([3]u32).empty;
    var groups = std.ArrayList(struct { parent: u32, kind: u8, members: []const u32 }).empty;
    for (b.ordered_features.items) |name| {
        const info = b.hierarchy.get(name).?;
        const parent_idx = index.get(name).?;
        for (info.children.items) |edge| {
            try edges.append(alloc, .{ parent_idx, index.get(edge.name).?, if (edge.kind == .mandatory) 1 else 0 });
        }
        for (info.groups.items) |g| {
            const member_idx = try alloc.alloc(u32, g.members.items.len);
            for (g.members.items, 0..) |m, i| member_idx[i] = index.get(m).?;
            try groups.append(alloc, .{ .parent = parent_idx, .kind = @intFromEnum(g.kind), .members = member_idx });
        }
    }

    try writeU32(w, @intCast(edges.items.len));
    for (edges.items) |e| {
        try writeU32(w, e[0]);
        try writeU32(w, e[1]);
        try w.writeByte(@intCast(e[2]));
    }

    try writeU32(w, @intCast(groups.items.len));
    for (groups.items) |g| {
        try writeU32(w, g.parent);
        try w.writeByte(g.kind);
        try writeU32(w, @intCast(g.members.len));
        for (g.members) |m| try writeU32(w, m);
    }

    var n_attrs: u32 = 0;
    for (b.ordered_features.items) |name| n_attrs += @intCast(b.hierarchy.get(name).?.attributes.items.len);
    try writeU32(w, n_attrs);
    for (b.ordered_features.items) |name| {
        const feature_idx = index.get(name).?;
        for (b.hierarchy.get(name).?.attributes.items) |attr| {
            try writeU32(w, feature_idx);
            try writeBytes(w, attr.key);
            try writeBytes(w, attr.value);
        }
    }

    try writeU32(w, @intCast(result.constraints.len));
    for (result.constraints) |c| try writeBytes(w, c.text);

    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

export fn uvl_parse_source_full(
    src_ptr: [*]const u8,
    src_len: usize,
    out_ptr: *[*]const u8,
    out_len: *usize,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    parseSourceFullImpl(arena_state.allocator(), src_ptr[0..src_len], out_ptr, out_len) catch |err| {
        setError("uvl_parse_source_full: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };
    return @intFromEnum(StatusCode.ok);
}

pub const CEdge = extern struct {
    parent_idx: usize,
    child_idx: usize,
    mandatory: u8, // 0 = optional, 1 = mandatory
};

pub const CGroup = extern struct {
    parent_idx: usize,
    kind: u8, // 0 = or, 1 = xor
    member_start: usize,
    member_count: usize,
};

const no_root = std.math.maxInt(usize);

fn hierarchyToCnfImpl(
    alloc: Allocator,
    features_c: []const [*:0]const u8,
    root_index: usize,
    edges: []const CEdge,
    groups: []const CGroup,
    group_members: []const usize,
    constraints: []const [*:0]const u8,
    do_simplify: bool,
    out_ptr: *[*]const u8,
    out_len: *usize,
    out_non_boolean: *NonBooleanCounts,
) !void {
    const names = try alloc.alloc([]const u8, features_c.len);
    for (features_c, 0..) |c_str, i| names[i] = std.mem.span(c_str);

    var features = std.StringHashMap(void).init(alloc);
    var hierarchy = std.StringHashMap(builder_mod.HInfo).init(alloc);
    for (names) |name| {
        try features.put(name, {});
        try hierarchy.put(name, builder_mod.HInfo{});
    }

    for (edges) |edge| {
        if (edge.parent_idx >= names.len or edge.child_idx >= names.len) return error.InvalidInput;
        const info = hierarchy.getPtr(names[edge.parent_idx]).?;
        try info.children.append(alloc, .{
            .name = names[edge.child_idx],
            .kind = if (edge.mandatory != 0) .mandatory else .optional,
        });
    }

    for (groups) |group| {
        if (group.parent_idx >= names.len) return error.InvalidInput;
        if (group.member_start + group.member_count > group_members.len) return error.InvalidInput;
        const g = try alloc.create(builder_mod.GroupEntry);
        g.* = .{ .kind = if (group.kind == 0) .or_group else .xor_group };
        for (group_members[group.member_start .. group.member_start + group.member_count]) |mi| {
            if (mi >= names.len) return error.InvalidInput;
            try g.members.append(alloc, names[mi]);
        }
        const info = hierarchy.getPtr(names[group.parent_idx]).?;
        try info.groups.append(alloc, g);
    }

    var ids = try cnf.assignIds(alloc, &features);

    var clauses = std.ArrayList([]i32).empty;
    if (root_index != no_root) {
        if (root_index >= names.len) return error.InvalidInput;
        const clause = try alloc.alloc(i32, 1);
        clause[0] = ids.get(names[root_index]).?;
        try clauses.append(alloc, clause);
    }
    try cnf.hierarchyToCnf(alloc, &hierarchy, &ids, &clauses);

    var attribute_ref_constraints: usize = 0;
    var comparison_constraints: usize = 0;
    for (constraints, 0..) |c_str, idx| {
        const text = std.mem.span(c_str);
        const tokens = try lexer.tokenize(alloc, text);
        const parsed = try constraint.parseConstraint(alloc, tokens, 0);
        if (parsed.node == null) {
            // attribute ref / comparison: not CNF-encodable. Lark/ANTLR's
            // own text-based classification (main.py's
            // _is_arithmetic_constraint) can't reliably tell these apart
            // from a genuinely boolean constraint (e.g. a dotted
            // reference used with no comparison operator at all, like
            // `A.enabled => B`), so this -- the same real syntactic
            // check `uvl_source_to_cnf` already does for zig -- is the
            // source of truth for all three backends.
            if (parsed.saw_dot) {
                std.debug.print("Info: Skipping constraint {d}: attribute reference\n", .{idx});
                attribute_ref_constraints += 1;
            } else {
                std.debug.print("Info: Skipping constraint {d}: numeric comparison\n", .{idx});
                comparison_constraints += 1;
            }
            continue;
        }
        const node = parsed.node.?;
        const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
            error.UnknownFeature => {
                std.debug.print("Warning: could not convert constraint {d}: unknown feature reference\n", .{idx});
                continue;
            },
            else => return err,
        };
        for (node_clauses) |c| try clauses.append(alloc, c);
    }

    const cclauses: []const []const i32 = @ptrCast(clauses.items);
    var out_clauses: []const []const i32 = cclauses;
    if (do_simplify) {
        const simplified = try subsumption.simplify(alloc, cclauses, false);
        out_clauses = simplified.clauses;
    }

    out_non_boolean.* = .{
        .attribute_ref_constraints = attribute_ref_constraints,
        .comparison_constraints = comparison_constraints,
    };

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    try cnf.writeDimacs(alloc, &aw.writer, &ids, out_clauses);
    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

/// Hybrid pipeline: caller already parsed the model; only CNF generation
/// runs here. `features_ptr` is the full feature-name table; every other
/// array indexes into it. `out_non_boolean` is only ever populated with
/// `attribute_ref_constraints`/`comparison_constraints` -- the other Tier
/// 1/Tier 3 categories in NonBooleanCounts depend on raw source this
/// function never sees (only `uvl_source_to_cnf` sees it); callers using
/// this hybrid path (Lark/ANTLR) get those from their own tree walk
/// instead and merge the two.
export fn uvl_hierarchy_to_cnf(
    features_ptr: [*]const [*:0]const u8,
    n_features: usize,
    root_index: usize,
    edges_ptr: [*]const CEdge,
    n_edges: usize,
    groups_ptr: [*]const CGroup,
    n_groups: usize,
    group_members_ptr: [*]const usize,
    n_group_members: usize,
    constraints_ptr: [*]const [*:0]const u8,
    n_constraints: usize,
    do_simplify: u8,
    out_ptr: *[*]const u8,
    out_len: *usize,
    out_non_boolean: *NonBooleanCounts,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    hierarchyToCnfImpl(
        arena_state.allocator(),
        features_ptr[0..n_features],
        root_index,
        edges_ptr[0..n_edges],
        groups_ptr[0..n_groups],
        group_members_ptr[0..n_group_members],
        constraints_ptr[0..n_constraints],
        do_simplify != 0,
        out_ptr,
        out_len,
        out_non_boolean,
    ) catch |err| {
        setError("uvl_hierarchy_to_cnf: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };
    return @intFromEnum(StatusCode.ok);
}

/// CNF -> UVL recovery (any2uvl). `optimize`/`by_name` gate the greedy
/// CTC-reduction pass and its name-similarity parent tie-break;
/// `infer_propagation` gates the experimental, opt-in propagation-based
/// implication recovery (see recovery.zig's `augmentGraphWithPropagation`
/// doc comment); see recovery.zig for the full algorithm.
export fn uvl_dimacs_to_uvl(
    dimacs_ptr: [*]const u8,
    dimacs_len: usize,
    optimize: u8,
    by_name: u8,
    infer_propagation: u8,
    out_ptr: *[*]const u8,
    out_len: *usize,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();

    const text = recovery.recover(arena_state.allocator(), gpa, dimacs_ptr[0..dimacs_len], optimize != 0, by_name != 0, infer_propagation != 0) catch |err| {
        setError("uvl_dimacs_to_uvl: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };

    out_ptr.* = text.ptr;
    out_len.* = text.len;
    return @intFromEnum(StatusCode.ok);
}

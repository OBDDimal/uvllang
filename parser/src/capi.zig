//! C ABI surface for the shared library, called from Python via ctypes.
//!
//! Three entry points:
//!   - `uvl_source_to_cnf`: full pipeline (lex, parse, build hierarchy,
//!     generate CNF) on raw UVL source text, writing DIMACS to an
//!     in-memory buffer instead of a file.
//!   - `uvl_hierarchy_to_cnf`: only the CNF-generation step, for callers
//!     that already parsed the file themselves and supply the hierarchy
//!     and constraints as flat arrays.
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
const recovery = @import("recovery.zig");

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
    too_complex = 4,
    out_of_memory = 5,
    invalid_input = 6,
};

fn statusForError(err: anyerror) StatusCode {
    return switch (err) {
        error.UnterminatedString, error.UnexpectedChar => .lex_error,
        error.UnexpectedToken, error.UnexpectedEnd => .parse_error,
        error.UnknownFeature => .unknown_feature,
        error.TooComplex => .too_complex,
        error.NoRoot, error.InvalidInput => .invalid_input,
        else => .out_of_memory,
    };
}

fn sourceToCnfImpl(alloc: Allocator, source: []const u8, out_ptr: *[*]const u8, out_len: *usize) !void {
    const tokens = try lexer.tokenize(alloc, source);
    const result = try parser.parseModel(alloc, tokens);
    var ids = try cnf.assignIds(alloc, &result.builder.features);

    var clauses = std.ArrayList([]i32).empty;
    if (result.builder.root) |root| {
        const clause = try alloc.alloc(i32, 1);
        clause[0] = ids.get(root).?;
        try clauses.append(alloc, clause);
    }
    try cnf.hierarchyToCnf(alloc, &result.builder.hierarchy, &ids, &clauses);

    for (result.constraints) |info| {
        if (info.node) |node| {
            const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: could not convert constraint at line {d}: unknown feature reference\n", .{info.text_line});
                    continue;
                },
                error.TooComplex => {
                    std.debug.print("Warning: could not convert constraint at line {d}: too complex to encode exactly within budget\n", .{info.text_line});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| try clauses.append(alloc, c);
        } else if (info.saw_dot) {
            std.debug.print("Info: Skipping constraint with attribute reference (line {d})\n", .{info.text_line});
        } else if (info.saw_comparison and info.saw_bool_op) {
            std.debug.print("Info: Skipping constraint with arithmetic comparison (line {d})\n", .{info.text_line});
        }
    }

    var kept = std.ArrayList([]const i32).empty;
    var n_taut: usize = 0;
    for (clauses.items) |c| {
        if (cnf.isTautological(c)) {
            n_taut += 1;
            continue;
        }
        try kept.append(alloc, c);
    }
    if (n_taut > 0) std.debug.print("Info: Removed {d} tautological clauses\n", .{n_taut});

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    try cnf.writeDimacs(alloc, &aw.writer, &ids, kept.items);
    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

export fn uvl_source_to_cnf(
    src_ptr: [*]const u8,
    src_len: usize,
    out_ptr: *[*]const u8,
    out_len: *usize,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    sourceToCnfImpl(arena_state.allocator(), src_ptr[0..src_len], out_ptr, out_len) catch |err| {
        setError("uvl_source_to_cnf: {t}", .{err});
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
    out_ptr: *[*]const u8,
    out_len: *usize,
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

    for (constraints, 0..) |c_str, idx| {
        const text = std.mem.span(c_str);
        const tokens = try lexer.tokenize(alloc, text);
        const parsed = try constraint.parseConstraint(alloc, tokens, 0);
        const node = parsed.node orelse continue; // attribute ref / comparison: not CNF-encodable
        const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
            error.UnknownFeature => {
                std.debug.print("Warning: could not convert constraint {d}: unknown feature reference\n", .{idx});
                continue;
            },
            error.TooComplex => {
                std.debug.print("Warning: could not convert constraint {d}: too complex to encode exactly within budget\n", .{idx});
                continue;
            },
            else => return err,
        };
        for (node_clauses) |c| try clauses.append(alloc, c);
    }

    var kept = std.ArrayList([]const i32).empty;
    for (clauses.items) |c| {
        if (cnf.isTautological(c)) continue;
        try kept.append(alloc, c);
    }

    var aw = std.Io.Writer.Allocating.init(gpa);
    defer aw.deinit();
    try cnf.writeDimacs(alloc, &aw.writer, &ids, kept.items);
    const owned = try aw.toOwnedSlice();
    out_ptr.* = owned.ptr;
    out_len.* = owned.len;
}

/// Hybrid pipeline: caller already parsed the model; only CNF generation
/// runs here. `features_ptr` is the full feature-name table; every other
/// array indexes into it.
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
    out_ptr: *[*]const u8,
    out_len: *usize,
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
        out_ptr,
        out_len,
    ) catch |err| {
        setError("uvl_hierarchy_to_cnf: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };
    return @intFromEnum(StatusCode.ok);
}

/// CNF -> UVL recovery (any2uvl). `optimize`/`by_name` gate the greedy
/// CTC-reduction pass and its name-similarity parent tie-break; see
/// recovery.zig for the full algorithm.
export fn uvl_dimacs_to_uvl(
    dimacs_ptr: [*]const u8,
    dimacs_len: usize,
    optimize: u8,
    by_name: u8,
    out_ptr: *[*]const u8,
    out_len: *usize,
) callconv(.c) i32 {
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();

    const text = recovery.recover(arena_state.allocator(), gpa, dimacs_ptr[0..dimacs_len], optimize != 0, by_name != 0) catch |err| {
        setError("uvl_dimacs_to_uvl: {t}", .{err});
        return @intFromEnum(statusForError(err));
    };

    out_ptr.* = text.ptr;
    out_len.* = text.len;
    return @intFromEnum(StatusCode.ok);
}

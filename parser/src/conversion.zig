//! `uvl2cnf --conversion` / `UVL(conversion=True)`: real UVLParser-paper
//! conversion strategies (Sundermann et al., SPLC'23, Table 1) for the two
//! Tier 1 constructs that have a clean, well-defined encoding -- group
//! cardinality and feature-local constraint attributes. See
//! docs/non_boolean_support.md.
//!
//! Feature cardinality (clone multiplicity) is deliberately NOT handled
//! here: the paper's own prescribed strategy ("repeated subtrees for
//! feature instances", citing Czarnecki & Kim) requires cloning a whole
//! subtree plus indexing any cross-tree constraint that references the
//! cloned feature, and the paper itself notes this interaction "is not
//! always clear" in the literature. That's future work, not built.

const std = @import("std");
const Allocator = std.mem.Allocator;
const builder_mod = @import("builder.zig");
const constraint = @import("constraint.zig");

/// Calls `emit(ctx, subset)` once per `r`-sized subset of `items`, in
/// increasing-index order. `scratch` is reused across calls as the
/// subset buffer -- `emit` must not retain it past the call it's passed
/// to (the emit functions below always copy immediately). `r == 0`
/// yields exactly one (empty) call.
fn forEachCombination(
    items: []const i32,
    r: usize,
    scratch: []i32,
    ctx: anytype,
    comptime emit: fn (@TypeOf(ctx), []const i32) anyerror!void,
) !void {
    try combinationsRec(items, r, 0, scratch, 0, ctx, emit);
}

fn combinationsRec(
    items: []const i32,
    r: usize,
    start: usize,
    scratch: []i32,
    depth: usize,
    ctx: anytype,
    comptime emit: fn (@TypeOf(ctx), []const i32) anyerror!void,
) !void {
    if (depth == r) {
        try emit(ctx, scratch[0..r]);
        return;
    }
    var i = start;
    while (i < items.len) : (i += 1) {
        scratch[depth] = items[i];
        try combinationsRec(items, r, i + 1, scratch, depth + 1, ctx, emit);
    }
}

const AtLeastCtx = struct {
    alloc: Allocator,
    parent_id: i32,
    clauses: *std.ArrayList([]i32),
};

/// `(¬parent ∨ subset...)`: parent selected implies at least one member of
/// this (k-min+1)-sized subset is selected -- across every such subset,
/// equivalent to "parent selected implies at least min of the k members
/// selected". min=1 degenerates to a single subset of size k, i.e.
/// exactly today's `or`-group clause.
fn emitAtLeast(ctx: AtLeastCtx, subset: []const i32) !void {
    const clause = try ctx.alloc.alloc(i32, subset.len + 1);
    clause[0] = -ctx.parent_id;
    @memcpy(clause[1..], subset);
    try ctx.clauses.append(ctx.alloc, clause);
}

const AtMostCtx = struct {
    alloc: Allocator,
    clauses: *std.ArrayList([]i32),
};

/// `(¬m1 ∨ … ∨ ¬m_{max+1})`: no (max+1)-sized subset can be fully
/// selected -- across every such subset, equivalent to "at most max of
/// the k members selected" (true regardless of parent: if parent isn't
/// selected, every member is already forced false by its own optional
/// child->parent edge, same convention as today's xor-group pairwise
/// exclusions, which are exactly this formula's max=1 case).
fn emitAtMost(ctx: AtMostCtx, subset: []const i32) !void {
    const clause = try ctx.alloc.alloc(i32, subset.len);
    for (subset, 0..) |m, i| clause[i] = -m;
    try ctx.clauses.append(ctx.alloc, clause);
}

/// Emits the combinatorial "enumerating constraints" encoding (paper
/// Table 1: Boolean/Group Cardinality -> Boolean Core) for one cardinality
/// group. A member or the parent missing from `ids` (shouldn't happen --
/// every parsed feature gets an id) is treated as "nothing to encode"
/// rather than an error, since this is a best-effort optional pass.
pub fn emitCardinalityGroupClauses(
    alloc: Allocator,
    cg: builder_mod.CardinalityGroup,
    ids: *const std.StringHashMap(i32),
    clauses: *std.ArrayList([]i32),
) !void {
    const parent_id = ids.get(cg.parent) orelse return;
    const member_ids = try alloc.alloc(i32, cg.members.items.len);
    for (cg.members.items, 0..) |m, i| member_ids[i] = ids.get(m) orelse return;
    const k = member_ids.len;
    if (k == 0) return;

    if (cg.range.min > 0) {
        const min: usize = @min(cg.range.min, @as(u32, @intCast(k)));
        const r = k - min + 1;
        const scratch = try alloc.alloc(i32, r);
        try forEachCombination(member_ids, r, scratch, AtLeastCtx{
            .alloc = alloc,
            .parent_id = parent_id,
            .clauses = clauses,
        }, emitAtLeast);
    }
    if (cg.range.max) |max| {
        if (max < k) {
            const r = max + 1;
            const scratch = try alloc.alloc(i32, r);
            try forEachCombination(member_ids, r, scratch, AtMostCtx{
                .alloc = alloc,
                .clauses = clauses,
            }, emitAtMost);
        }
    }
}

/// Converts every already-extracted `FeatureLocalConstraint` with a valid
/// Boolean AST (`.node != null`) into clauses via the same
/// `constraint.generateClauses` top-level constraints use. Entries with
/// `.node == null` (a dotted attribute reference or numeric comparison --
/// the paper's own Tier-2-equivalent fallback: "drop instead of
/// converting") are left alone; the caller's existing
/// `constraint_attribute_count` warning already covers them.
pub fn emitFeatureLocalConstraintClauses(
    alloc: Allocator,
    flcs: []const builder_mod.FeatureLocalConstraint,
    ids: *const std.StringHashMap(i32),
    clauses: *std.ArrayList([]i32),
) !void {
    for (flcs) |flc| {
        const node = flc.node orelse continue;
        const node_clauses = constraint.generateClauses(alloc, ids, node) catch |err| switch (err) {
            error.UnknownFeature => continue,
            else => return err,
        };
        for (node_clauses) |c| try clauses.append(alloc, c);
    }
}

test "cardinality [1..k] matches a plain or-group clause" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var ids = std.StringHashMap(i32).init(alloc);
    try ids.put("P", 1);
    try ids.put("A", 2);
    try ids.put("B", 3);
    try ids.put("C", 4);

    var cg = builder_mod.CardinalityGroup{ .parent = "P", .range = .{ .min = 1, .max = 3 } };
    try cg.members.append(alloc, "A");
    try cg.members.append(alloc, "B");
    try cg.members.append(alloc, "C");

    var clauses = std.ArrayList([]i32).empty;
    try emitCardinalityGroupClauses(alloc, cg, &ids, &clauses);

    // max == k (3), so no "at most" clauses; min == 1 gives exactly one
    // "at least" clause: (-1 2 3 4), same shape as an or-group.
    try std.testing.expectEqual(@as(usize, 1), clauses.items.len);
    const c = clauses.items[0];
    try std.testing.expectEqual(@as(usize, 4), c.len);
    try std.testing.expectEqual(@as(i32, -1), c[0]);
}

test "cardinality [1..1] matches or-clause plus xor's pairwise exclusions" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var ids = std.StringHashMap(i32).init(alloc);
    try ids.put("P", 1);
    try ids.put("A", 2);
    try ids.put("B", 3);
    try ids.put("C", 4);

    var cg = builder_mod.CardinalityGroup{ .parent = "P", .range = .{ .min = 1, .max = 1 } };
    try cg.members.append(alloc, "A");
    try cg.members.append(alloc, "B");
    try cg.members.append(alloc, "C");

    var clauses = std.ArrayList([]i32).empty;
    try emitCardinalityGroupClauses(alloc, cg, &ids, &clauses);

    // 1 "at least" clause (-1 2 3 4) + C(3,2)=3 pairwise "at most"
    // clauses -- exactly an xor group's (¬p∨c1∨c2∨c3) + pairwise (¬ci∨¬cj).
    try std.testing.expectEqual(@as(usize, 4), clauses.items.len);
    var pairwise_count: usize = 0;
    for (clauses.items) |c| {
        if (c.len == 2) pairwise_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), pairwise_count);
}

test "cardinality [2..*] emits only the at-least side" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var ids = std.StringHashMap(i32).init(alloc);
    try ids.put("P", 1);
    try ids.put("A", 2);
    try ids.put("B", 3);
    try ids.put("C", 4);

    var cg = builder_mod.CardinalityGroup{ .parent = "P", .range = .{ .min = 2, .max = null } };
    try cg.members.append(alloc, "A");
    try cg.members.append(alloc, "B");
    try cg.members.append(alloc, "C");

    var clauses = std.ArrayList([]i32).empty;
    try emitCardinalityGroupClauses(alloc, cg, &ids, &clauses);

    // r = k - min + 1 = 3 - 2 + 1 = 2 -> C(3,2) = 3 "at least" clauses,
    // each of length 3 (-parent + 2 members); no "at most" side at all.
    try std.testing.expectEqual(@as(usize, 3), clauses.items.len);
    for (clauses.items) |c| try std.testing.expectEqual(@as(usize, 3), c.len);
}

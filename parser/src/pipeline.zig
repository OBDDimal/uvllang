//! Shared source -> CNF pipeline. `uvl2cnf` (main.zig) and
//! `uvl_source_to_cnf` (capi.zig, the Python API's zig backend) used to
//! each hand-roll their own copy of "assign ids, emit the root/hierarchy/
//! optional --conversion clauses, walk every top-level constraint into
//! clauses or a counted+warned skip" -- identical in substance but free
//! to drift (and already had: the two printed the same non-Boolean
//! warnings in different orders relative to each other and to
//! --simplify's own messages). This module is the one copy of that
//! logic both now call, so the CLI and the library can never again
//! disagree about what a given model warns about or produces.

const std = @import("std");
const Allocator = std.mem.Allocator;
const parser = @import("parser.zig");
const cnf = @import("cnf.zig");
const constraint = @import("constraint.zig");
const conversion = @import("conversion.zig");
const builder_mod = @import("builder.zig");

pub const ConstraintCounts = struct {
    attribute_ref_constraints: usize = 0,
    comparison_constraints: usize = 0,
};

/// Counts of constructs above the plain Boolean language level -- see
/// docs/non_boolean_support.md. Tier 1 (corrupts CNF correctness or loses
/// a real constraint) first, then Tier 2 (a constraint is dropped), then
/// Tier 3 (decorative metadata only). This is capi.zig's Python-facing
/// struct (an `extern struct` for a stable C ABI layout) -- defined here
/// so `uvl2cnf`'s `--strict` (main.zig) and `UVL(drop_non_boolean=False)`
/// (capi.zig) share one `isThreatening` instead of each tracking the
/// threatening-category list on its own.
pub const NonBooleanCounts = extern struct {
    cardinality_groups: usize = 0,
    constraint_attributes: usize = 0,
    cardinality_features: usize = 0,
    attribute_ref_constraints: usize = 0,
    comparison_constraints: usize = 0,
    typed_features: usize = 0,
    attributed_features: usize = 0,

    /// True iff a caller that wants to fail instead of silently
    /// continuing (`uvl2cnf --strict`, `UVL(drop_non_boolean=False)`)
    /// should refuse: any Tier 1/2 count is nonzero, except group
    /// cardinality and constraint attributes are exempt when
    /// `do_conversion` actually converts them instead of dropping them.
    /// Tier 3 (typed/attributed features) never blocks.
    pub fn isThreatening(self: NonBooleanCounts, do_conversion: bool) bool {
        if (self.cardinality_features > 0) return true;
        if (self.attribute_ref_constraints > 0) return true;
        if (self.comparison_constraints > 0) return true;
        if (!do_conversion) {
            if (self.cardinality_groups > 0) return true;
            if (self.constraint_attributes > 0) return true;
        }
        return false;
    }
};

/// Merges a `Builder`'s own Tier 1/3 counts with `buildClauses`'
/// Tier 2 counts into one `NonBooleanCounts`.
pub fn mergeNonBooleanCounts(b: *const builder_mod.Builder, counts: ConstraintCounts) NonBooleanCounts {
    return .{
        .cardinality_groups = b.cardinality_group_count,
        .constraint_attributes = b.constraint_attribute_count,
        .cardinality_features = b.cardinality_feature_count,
        .attribute_ref_constraints = counts.attribute_ref_constraints,
        .comparison_constraints = counts.comparison_constraints,
        .typed_features = b.typed_feature_count,
        .attributed_features = b.attributed_feature_count,
    };
}

pub const BuildResult = struct {
    ids: std.StringHashMap(i32),
    clauses: std.ArrayList([]i32),
    counts: ConstraintCounts,
};

/// Assigns ids, then emits, in order: the root unit clause, the
/// hierarchy's own clauses, the `--conversion`/`conversion=True` clauses
/// when `do_conversion` (group cardinality, feature-local constraint
/// attributes -- see conversion.zig), and every Boolean-encodable
/// top-level constraint's clauses. A constraint that isn't
/// Boolean-encodable prints the same per-constraint warning either
/// caller already printed and is tallied into the returned `counts`
/// instead of being silently skipped. Never simplifies -- a caller that
/// wants `--simplify` runs `subsumption.simplify` over the returned
/// clauses itself, since that decision is orthogonal to everything here.
pub fn buildClauses(alloc: Allocator, result: *const parser.ParseResult, do_conversion: bool) !BuildResult {
    var ids = try cnf.assignIds(alloc, &result.builder.features);

    var clauses = std.ArrayList([]i32).empty;
    if (result.builder.root) |root| {
        const clause = try alloc.alloc(i32, 1);
        clause[0] = ids.get(root).?;
        try clauses.append(alloc, clause);
    }
    try cnf.hierarchyToCnf(alloc, &result.builder.hierarchy, &ids, &clauses);

    if (do_conversion) {
        for (result.builder.cardinality_groups.items) |cg| {
            try conversion.emitCardinalityGroupClauses(alloc, cg, &ids, &clauses);
        }
        try conversion.emitFeatureLocalConstraintClauses(alloc, result.builder.feature_local_constraints.items, &ids, &clauses);
    }

    var counts = ConstraintCounts{};
    for (result.constraints) |info| {
        if (info.node) |node| {
            const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: could not convert constraint at line {d}: unknown feature reference\n", .{info.text_line});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| try clauses.append(alloc, c);
        } else if (info.saw_dot) {
            std.debug.print("Info: Skipping constraint with attribute reference (line {d})\n", .{info.text_line});
            counts.attribute_ref_constraints += 1;
        } else if (info.saw_comparison and info.saw_bool_op) {
            std.debug.print("Info: Skipping constraint with arithmetic comparison (line {d})\n", .{info.text_line});
            counts.comparison_constraints += 1;
        } else if (info.saw_comparison) {
            std.debug.print("Info: Skipping constraint (line {d}): a bare comparison isn't Boolean-encodable\n", .{info.text_line});
            counts.comparison_constraints += 1;
        }
    }

    return .{ .ids = ids, .clauses = clauses, .counts = counts };
}

/// Prints the "construct above the plain Boolean level" summary
/// warnings -- Tier 1 (group/feature cardinality, feature-local
/// constraint attributes), Tier 2 (attribute-ref/comparison constraints,
/// from `counts`), Tier 3 (typed/attributed features) -- in one
/// canonical order. See docs/non_boolean_support.md.
pub fn printNonBooleanWarnings(b: *const builder_mod.Builder, counts: ConstraintCounts, do_conversion: bool) void {
    if (b.cardinality_group_count > 0) {
        if (do_conversion) {
            std.debug.print("Info: {d} group(s) use a cardinality range ([i..j]); converted to enumerated Boolean clauses\n", .{b.cardinality_group_count});
        } else {
            std.debug.print("Warning: {d} group(s) use a cardinality range ([i..j]); the bound is not enforced in the CNF (pass --conversion to encode it)\n", .{b.cardinality_group_count});
        }
    }
    if (b.constraint_attribute_count > 0) {
        if (do_conversion) {
            std.debug.print("Info: {d} feature-local `constraint`/`constraints` attribute(s) converted into ordinary constraints\n", .{b.constraint_attribute_count});
        } else {
            std.debug.print("Warning: {d} feature-local `constraint`/`constraints` attribute(s) were dropped, not converted (pass --conversion to extract them)\n", .{b.constraint_attribute_count});
        }
    }
    if (b.cardinality_feature_count > 0) {
        std.debug.print("Warning: {d} feature(s) use a clone cardinality range ([i..j]); clone instances are not encoded (not supported by --conversion yet)\n", .{b.cardinality_feature_count});
    }
    if (counts.attribute_ref_constraints > 0) {
        std.debug.print("Info: Ignored {d} constraint(s) referencing a feature attribute\n", .{counts.attribute_ref_constraints});
    }
    if (counts.comparison_constraints > 0) {
        std.debug.print("Info: Ignored {d} constraint(s) containing a numeric comparison\n", .{counts.comparison_constraints});
    }
    if (b.typed_feature_count > 0) {
        std.debug.print("Info: {d} feature(s) declare a non-Boolean type; ignored for CNF purposes\n", .{b.typed_feature_count});
    }
    if (b.attributed_feature_count > 0) {
        std.debug.print("Info: {d} feature(s) carry value attributes; ignored for CNF purposes\n", .{b.attributed_feature_count});
    }
}

const lexer = @import("lexer.zig");

fn buildResult(alloc: Allocator, src: []const u8) !parser.ParseResult {
    const tokens = try lexer.tokenize(alloc, src);
    return parser.parseModel(alloc, tokens);
}

test "NonBooleanCounts.isThreatening: cardinality_groups/constraint_attributes are exempt only under conversion" {
    const counts = NonBooleanCounts{ .cardinality_groups = 1 };
    try std.testing.expect(counts.isThreatening(false));
    try std.testing.expect(!counts.isThreatening(true));

    const attrs = NonBooleanCounts{ .constraint_attributes = 1 };
    try std.testing.expect(attrs.isThreatening(false));
    try std.testing.expect(!attrs.isThreatening(true));
}

test "NonBooleanCounts.isThreatening: cardinality_features/attribute_ref/comparison always block" {
    try std.testing.expect((NonBooleanCounts{ .cardinality_features = 1 }).isThreatening(true));
    try std.testing.expect((NonBooleanCounts{ .attribute_ref_constraints = 1 }).isThreatening(true));
    try std.testing.expect((NonBooleanCounts{ .comparison_constraints = 1 }).isThreatening(true));
}

test "NonBooleanCounts.isThreatening: Tier 3 (typed/attributed features) never blocks" {
    const counts = NonBooleanCounts{ .typed_features = 1, .attributed_features = 1 };
    try std.testing.expect(!counts.isThreatening(false));
    try std.testing.expect(!counts.isThreatening(true));
}

test "NonBooleanCounts.isThreatening: all-zero counts never block" {
    try std.testing.expect(!(NonBooleanCounts{}).isThreatening(false));
    try std.testing.expect(!(NonBooleanCounts{}).isThreatening(true));
}

test "buildClauses: root, hierarchy, and a boolean constraint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        mandatory
        \\            A
        \\
        \\constraints
        \\    A => Root
        \\
    ;
    const result = try buildResult(alloc, src);
    const built = try buildClauses(alloc, &result, false);

    try std.testing.expectEqual(@as(usize, 0), built.counts.attribute_ref_constraints);
    try std.testing.expectEqual(@as(usize, 0), built.counts.comparison_constraints);
    // root unit clause + 2 hierarchy clauses (mandatory both ways) + 1
    // constraint clause (subsumed-in-content but not deduped here, this
    // pass doesn't simplify).
    try std.testing.expectEqual(@as(usize, 4), built.clauses.items.len);
}

test "buildClauses: dotted/comparison constraints are counted, not included" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root {weight 3}
        \\        optional
        \\            A
        \\
        \\constraints
        \\    A.enabled => Root
        \\    1 > 0
        \\
    ;
    const result = try buildResult(alloc, src);
    const built = try buildClauses(alloc, &result, false);

    // A bare dotted reference used as a plain boolean operand (no
    // comparison at all) is the attribute_ref case; a numeric comparison
    // -- whether or not it also involves a dotted reference, e.g.
    // `Root.weight > 1` -- is the comparison case instead (saw_comparison
    // is set unconditionally by parseAtom's comparison branch, which
    // never separately checks operand dottedness).
    try std.testing.expectEqual(@as(usize, 1), built.counts.attribute_ref_constraints);
    try std.testing.expectEqual(@as(usize, 1), built.counts.comparison_constraints);
    // root unit clause + 1 hierarchy clause (A optional child of Root);
    // neither dropped constraint contributes a clause.
    try std.testing.expectEqual(@as(usize, 2), built.clauses.items.len);
}

test "buildClauses: --conversion encodes a group-cardinality bound" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        [1..1]
        \\            A
        \\            B
        \\
    ;
    const result = try buildResult(alloc, src);

    const without = try buildClauses(alloc, &result, false);
    const with = try buildClauses(alloc, &result, true);
    try std.testing.expect(with.clauses.items.len > without.clauses.items.len);
}

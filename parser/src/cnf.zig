const std = @import("std");
const Allocator = std.mem.Allocator;
const builder_mod = @import("builder.zig");
const HInfo = builder_mod.HInfo;
const GroupKind = builder_mod.GroupKind;

/// Assigns 1-indexed ids by sorting the distinct feature-name set
/// lexicographically -- mirrors `to_cnf`'s
/// `{feature: i+1 for i, feature in enumerate(sorted(set(self.features)))}`,
/// which is what keeps ids persistent across a hierarchy rebuild.
pub fn assignIds(alloc: Allocator, features: *const std.StringHashMap(void)) !std.StringHashMap(i32) {
    var names = std.ArrayList([]const u8).empty;
    defer names.deinit(alloc);
    var it = features.keyIterator();
    while (it.next()) |k| try names.append(alloc, k.*);
    std.mem.sort([]const u8, names.items, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);

    var ids = std.StringHashMap(i32).init(alloc);
    for (names.items, 0..) |name, i| {
        try ids.put(name, @intCast(i + 1));
    }
    return ids;
}

/// Direct port of UVL._hierarchy_to_cnf: a mandatory/optional child
/// contributes a child->parent implication (plus parent->child for
/// mandatory), and an or/xor group contributes the parent-implies-any-member
/// clause (plus the pairwise exclusions for xor). mandatory_children /
/// optional_children group entries are recorded by the builder but never
/// reach a clause here -- their constraint is already fully captured by the
/// child edges above, exactly like the Python implementation.
pub fn hierarchyToCnf(
    alloc: Allocator,
    hierarchy: *const std.StringHashMap(HInfo),
    ids: *const std.StringHashMap(i32),
    clauses: *std.ArrayList([]i32),
) !void {
    var it = hierarchy.iterator();
    while (it.next()) |entry| {
        const feature_id = ids.get(entry.key_ptr.*).?;
        const info = entry.value_ptr;

        for (info.children.items) |edge| {
            const child_id = ids.get(edge.name).?;
            var clause = try alloc.alloc(i32, 2);
            clause[0] = -child_id;
            clause[1] = feature_id;
            try clauses.append(alloc, clause);
            if (edge.kind == .mandatory) {
                var mclause = try alloc.alloc(i32, 2);
                mclause[0] = -feature_id;
                mclause[1] = child_id;
                try clauses.append(alloc, mclause);
            }
        }

        for (info.groups.items) |group| {
            if (group.kind != .or_group and group.kind != .xor_group) continue;
            var clause = try alloc.alloc(i32, group.members.items.len + 1);
            clause[0] = -feature_id;
            for (group.members.items, 0..) |member, i| {
                clause[i + 1] = ids.get(member).?;
            }
            try clauses.append(alloc, clause);

            if (group.kind == .xor_group) {
                const n = group.members.items.len;
                var i: usize = 0;
                while (i < n) : (i += 1) {
                    var j: usize = i + 1;
                    while (j < n) : (j += 1) {
                        var pair = try alloc.alloc(i32, 2);
                        pair[0] = -ids.get(group.members.items[i]).?;
                        pair[1] = -ids.get(group.members.items[j]).?;
                        try clauses.append(alloc, pair);
                    }
                }
            }
        }
    }
}

/// A clause containing both a literal and its negation is always true, so
/// it carries zero real constraint information -- to_cnf() strips these;
/// mirror that here so DIMACS output matches byte-for-byte.
pub fn isTautological(clause: []const i32) bool {
    for (clause) |lit| {
        for (clause) |other| {
            if (other == -lit) return true;
        }
    }
    return false;
}

pub fn writeDimacs(
    alloc: Allocator,
    w: *std.Io.Writer,
    ids: *const std.StringHashMap(i32),
    clauses: []const []const i32,
) !void {
    const names = try alloc.alloc([]const u8, ids.count());
    defer alloc.free(names);
    var it = ids.iterator();
    while (it.next()) |entry| {
        names[@intCast(entry.value_ptr.* - 1)] = entry.key_ptr.*;
    }
    for (names, 0..) |name, i| {
        try w.print("c {d} {s}\n", .{ i + 1, name });
    }
    try w.print("p cnf {d} {d}\n", .{ names.len, clauses.len });
    for (clauses) |clause| {
        for (clause) |lit| {
            try w.print("{d} ", .{lit});
        }
        try w.print("0\n", .{});
    }
}

test "tautology detection" {
    try std.testing.expect(isTautological(&[_]i32{ 1, -1, 2 }));
    try std.testing.expect(!isTautological(&[_]i32{ 1, 2, -3 }));
}

test "assignIds sorts lexicographically" {
    const alloc = std.testing.allocator;
    var features = std.StringHashMap(void).init(alloc);
    defer features.deinit();
    try features.put("Zebra", {});
    try features.put("Apple", {});
    try features.put("Mango", {});

    var ids = try assignIds(alloc, &features);
    defer ids.deinit();
    try std.testing.expectEqual(@as(i32, 1), ids.get("Apple").?);
    try std.testing.expectEqual(@as(i32, 2), ids.get("Mango").?);
    try std.testing.expectEqual(@as(i32, 3), ids.get("Zebra").?);
}

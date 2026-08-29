const std = @import("std");
const Allocator = std.mem.Allocator;

pub const ChildType = enum { mandatory, optional };

pub const ChildEdge = struct {
    name: []const u8,
    kind: ChildType,
};

pub const GroupKind = enum { or_group, xor_group, mandatory_children, optional_children };

pub const GroupEntry = struct {
    kind: GroupKind,
    members: std.ArrayList([]const u8) = .empty,
};

pub const AttributeEntry = struct {
    key: []const u8,
    /// Raw source-text span of the value. A bare key with no value (e.g.
    /// `abstract`) is never turned into an AttributeEntry at all -- see
    /// parser.zig's parseAttribute -- matching LarkFeatureExtractor/
    /// AntlrFeatureExtractor, which don't record those either. Values are
    /// stored as raw token/getText() text rather than typed Python values,
    /// also matching those two.
    value: []const u8,
};

pub const HInfo = struct {
    children: std.ArrayList(ChildEdge) = .empty,
    groups: std.ArrayList(*GroupEntry) = .empty,
    parent: ?[]const u8 = null,
    /// Raw keyword text ("String"/"Boolean"/"Integer"/"Real"), matching
    /// UVL.feature_types's values in the Python implementation.
    feature_type: ?[]const u8 = null,
    attributes: std.ArrayList(AttributeEntry) = .empty,
};

/// Tracks current_feature/current_group state while the parser walks the
/// features section, building the same hierarchy shape
/// UVL.builder().feature_hierarchy produces in the Python implementation.
/// Cardinality groups never call startGroup/endGroup, so their members
/// become plain optional children with no group clause.
pub const Builder = struct {
    alloc: Allocator,
    root: ?[]const u8 = null,
    hierarchy: std.StringHashMap(HInfo),
    features: std.StringHashMap(void),
    current_feature: ?[]const u8 = null,
    feature_stack: std.ArrayList(?[]const u8) = .empty,
    current_group: ?*GroupEntry = null,
    group_stack: std.ArrayList(*GroupEntry) = .empty,
    /// Document order, matching Lark/ANTLR's `.features` (a plain list
    /// built via sequential appends during their tree walk). `features`
    /// below is unordered (a StringHashMap), kept for the O(1) membership
    /// checks callers already rely on.
    ordered_features: std.ArrayList([]const u8) = .empty,

    /// Counts of constructs above the plain Boolean language level, all
    /// silently mishandled today (see docs/non_boolean_support.md):
    /// Tier 1 (corrupts CNF correctness or loses a real constraint) --
    /// `cardinality_group_count`, `constraint_attribute_count`,
    /// `cardinality_feature_count`; Tier 3 (decorative metadata) --
    /// `typed_feature_count`, `attributed_feature_count`. Tier 2
    /// (attribute-reference/comparison constraints) is counted per-constraint
    /// in capi.zig/main.zig instead, not here.
    cardinality_group_count: usize = 0,
    constraint_attribute_count: usize = 0,
    cardinality_feature_count: usize = 0,
    typed_feature_count: usize = 0,
    attributed_feature_count: usize = 0,

    pub fn init(alloc: Allocator) Builder {
        return .{
            .alloc = alloc,
            .hierarchy = std.StringHashMap(HInfo).init(alloc),
            .features = std.StringHashMap(void).init(alloc),
        };
    }

    pub fn startFeature(b: *Builder, name: []const u8) !void {
        if (b.root == null) b.root = name;

        const gop = try b.hierarchy.getOrPut(name);
        if (!gop.found_existing) {
            gop.value_ptr.* = HInfo{ .parent = b.current_feature };
        }
        try b.features.put(name, {});
        try b.ordered_features.append(b.alloc, name);

        var child_kind: ChildType = .optional;
        if (b.current_group) |g| {
            if (g.kind == .mandatory_children) child_kind = .mandatory;
            try g.members.append(b.alloc, name);
        }

        if (b.current_feature) |cf| {
            const info = b.hierarchy.getPtr(cf).?;
            try info.children.append(b.alloc, .{ .name = name, .kind = child_kind });
        }

        try b.feature_stack.append(b.alloc, b.current_feature);
        b.current_feature = name;
    }

    pub fn setFeatureType(b: *Builder, name: []const u8, type_text: []const u8) void {
        const info = b.hierarchy.getPtr(name) orelse return;
        info.feature_type = type_text;
    }

    pub fn addAttribute(b: *Builder, name: []const u8, key: []const u8, value: []const u8) !void {
        const info = b.hierarchy.getPtr(name) orelse return;
        try info.attributes.append(b.alloc, .{ .key = key, .value = value });
    }

    pub fn endFeature(b: *Builder) void {
        if (b.feature_stack.pop()) |prev| {
            b.current_feature = prev;
        } else {
            b.current_feature = null;
        }
    }

    pub fn startGroup(b: *Builder, kind: GroupKind) !void {
        const cf = b.current_feature orelse return;
        const g = try b.alloc.create(GroupEntry);
        g.* = .{ .kind = kind };
        try b.group_stack.append(b.alloc, g);
        b.current_group = g;
        const info = b.hierarchy.getPtr(cf).?;
        try info.groups.append(b.alloc, g);
    }

    pub fn endGroup(b: *Builder) void {
        _ = b.group_stack.pop();
        b.current_group = if (b.group_stack.items.len > 0) b.group_stack.items[b.group_stack.items.len - 1] else null;
    }
};

test "plain hierarchy: mandatory child + or-group siblings" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var b = Builder.init(alloc);

    try b.startFeature("Root");
    try b.startGroup(.mandatory_children);
    try b.startFeature("A");
    b.endFeature();
    b.endGroup();
    try b.startGroup(.or_group);
    try b.startFeature("B");
    b.endFeature();
    try b.startFeature("C");
    b.endFeature();
    b.endGroup();
    b.endFeature();

    try std.testing.expectEqualStrings("Root", b.root.?);
    const root_info = b.hierarchy.get("Root").?;
    try std.testing.expectEqual(@as(usize, 3), root_info.children.items.len);
    try std.testing.expectEqual(ChildType.mandatory, root_info.children.items[0].kind);
    try std.testing.expectEqual(ChildType.optional, root_info.children.items[1].kind);
    try std.testing.expectEqual(@as(usize, 2), root_info.groups.items.len);
    try std.testing.expectEqual(GroupKind.or_group, root_info.groups.items[1].kind);
    try std.testing.expectEqual(@as(usize, 2), root_info.groups.items[1].members.items.len);
}

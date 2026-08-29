const std = @import("std");
const Allocator = std.mem.Allocator;
const tok = @import("token.zig");
const Token = tok.Token;
const Kind = tok.Kind;
const builder_mod = @import("builder.zig");
const Builder = builder_mod.Builder;
const constraint = @import("constraint.zig");

pub const ParseError = error{ UnexpectedToken, UnexpectedEnd } || Allocator.Error || constraint.ParseError;

const P = struct {
    alloc: Allocator,
    tokens: []const Token,
    pos: usize = 0,

    fn cur(p: *P) Token {
        return p.tokens[p.pos];
    }

    fn check(p: *P, k: Kind) bool {
        return p.cur().kind == k;
    }

    fn advance(p: *P) Token {
        const t = p.tokens[p.pos];
        if (p.pos + 1 < p.tokens.len) p.pos += 1;
        return t;
    }

    fn expect(p: *P, k: Kind) !void {
        if (!p.check(k)) return ParseError.UnexpectedToken;
        _ = p.advance();
    }

    fn skipNewlineIfPresent(p: *P) void {
        if (p.check(.newline)) _ = p.advance();
    }
};

fn isReferenceStart(k: Kind) bool {
    return k == .id_strict or k == .id_not_strict;
}

fn parseReferenceName(p: *P) ![]const u8 {
    if (!isReferenceStart(p.cur().kind)) return ParseError.UnexpectedToken;
    var name = std.ArrayList(u8).empty;
    try name.appendSlice(p.alloc, p.advance().text);
    while (p.check(.dot)) {
        _ = p.advance();
        try name.appendSlice(p.alloc, ".");
        if (!isReferenceStart(p.cur().kind)) return ParseError.UnexpectedToken;
        try name.appendSlice(p.alloc, p.advance().text);
    }
    return name.toOwnedSlice(p.alloc);
}

fn isFeatureType(k: Kind) bool {
    return switch (k) {
        .string_key, .boolean_key, .integer_key, .real_key => true,
        else => false,
    };
}

/// Reconstructs the raw source text spanning `first`..`last` inclusive.
/// Every Token.text is already a slice into the original source buffer and
/// tokens within one span are always contiguous in it, so this needs no
/// separate reference to that buffer -- just pointer arithmetic between
/// the two slices.
fn spanText(first: Token, last: Token) []const u8 {
    const start_addr = @intFromPtr(first.text.ptr);
    const end_addr = @intFromPtr(last.text.ptr) + last.text.len;
    return first.text.ptr[0 .. end_addr - start_addr];
}

fn isValueStart(k: Kind) bool {
    return switch (k) {
        .boolean_lit, .float, .integer, .string_lit, .id_not_strict, .lbrace, .lbrack => true,
        else => false,
    };
}

/// Consumes a balanced bracketed span starting at the current token (which
/// must be lparen/lbrack/lbrace), returning its raw source text. Used both
/// to reconstruct vector/nested-attributes attribute values, and to skip a
/// `constraints { [...] }` list attribute's body without extracting it
/// (LarkFeatureExtractor doesn't either -- see parseAttribute below).
fn skipBalanced(p: *P) ParseError![]const u8 {
    const first = p.cur();
    var depth: i32 = 0;
    var last = first;
    while (true) {
        if (p.check(.eof)) return ParseError.UnexpectedEnd;
        const t = p.advance();
        last = t;
        switch (t.kind) {
            .lparen, .lbrack, .lbrace => depth += 1,
            .rparen, .rbrack, .rbrace => depth -= 1,
            else => {},
        }
        if (depth == 0) break;
    }
    return spanText(first, last);
}

/// Skips a bare `constraint <expr>` attribute body up to the top-level
/// comma/close-brace that ends it (tracking paren depth only -- the only
/// bracket a constraint expression can contain, e.g. `sum(A, B)`).
fn skipUntilCommaOrRbrace(p: *P) ParseError![]const u8 {
    const first = p.cur();
    var depth: i32 = 0;
    var last = first;
    while (true) {
        if (p.check(.eof)) return ParseError.UnexpectedEnd;
        if (depth == 0 and (p.check(.comma) or p.check(.rbrace))) break;
        const t = p.advance();
        last = t;
        switch (t.kind) {
            .lparen => depth += 1,
            .rparen => depth -= 1,
            else => {},
        }
    }
    return spanText(first, last);
}

fn parseValue(p: *P) ParseError![]const u8 {
    return switch (p.cur().kind) {
        .boolean_lit, .float, .integer, .string_lit, .id_not_strict => p.advance().text,
        .lbrace, .lbrack => try skipBalanced(p),
        else => ParseError.UnexpectedToken,
    };
}

/// attribute: value_attribute | constraint_attribute
/// Only value_attribute is extracted into feature_attributes, matching
/// LarkFeatureExtractor._extract_attributes/AntlrFeatureExtractor's
/// enterValueAttribute, which never handle constraint_attribute either --
/// constraint/constraints attribute bodies are parsed just far enough to
/// skip them correctly.
fn parseAttribute(p: *P, b: *Builder, feature_name: []const u8) ParseError!void {
    switch (p.cur().kind) {
        .constraint_key => {
            _ = p.advance();
            _ = try skipUntilCommaOrRbrace(p);
            b.constraint_attribute_count += 1;
        },
        .constraints_key => {
            _ = p.advance();
            if (p.check(.lbrack)) _ = try skipBalanced(p);
            b.constraint_attribute_count += 1;
        },
        else => {
            // value_attribute: key value?. A bare key with no value (e.g.
            // `abstract`) matches LarkFeatureExtractor/AntlrFeatureExtractor:
            // neither records it into feature_attributes either (both only
            // call add_attribute when `key and value` are both present) --
            // so it's consumed here but not added.
            if (!isReferenceStart(p.cur().kind)) return ParseError.UnexpectedToken;
            const key = p.advance().text;
            if (isValueStart(p.cur().kind)) {
                const value = try parseValue(p);
                try b.addAttribute(feature_name, key, value);
            }
        },
    }
}

/// attributes: OPEN_BRACE (attribute (COMMA attribute)*)? CLOSE_BRACE
fn parseAttributes(p: *P, b: *Builder, feature_name: []const u8) ParseError!void {
    try p.expect(.lbrace);
    if (!p.check(.rbrace)) {
        while (true) {
            try parseAttribute(p, b, feature_name);
            if (!p.check(.comma)) break;
            _ = p.advance();
        }
    }
    try p.expect(.rbrace);
    if (b.hierarchy.getPtr(feature_name).?.attributes.items.len > 0) {
        b.attributed_feature_count += 1;
    }
}

fn parseFeature(p: *P, b: *Builder) ParseError!void {
    var feature_type: ?[]const u8 = null;
    if (isFeatureType(p.cur().kind)) {
        feature_type = p.advance().text;
        b.typed_feature_count += 1;
    }

    const name = try parseReferenceName(p);
    try b.startFeature(name);
    defer b.endFeature();
    if (feature_type) |t| b.setFeatureType(name, t);

    if (p.check(.cardinality_key)) {
        _ = p.advance();
        try p.expect(.cardinality_lit);
        b.cardinality_feature_count += 1;
    }
    if (p.check(.lbrace)) try parseAttributes(p, b, name);

    try p.expect(.newline);

    if (p.check(.indent)) {
        _ = p.advance();
        while (!p.check(.dedent)) {
            try parseGroup(p, b);
        }
        try p.expect(.dedent);
    }
}

fn parseGroupSpec(p: *P, b: *Builder) ParseError!void {
    try p.expect(.newline);
    try p.expect(.indent);
    while (!p.check(.dedent)) {
        try parseFeature(p, b);
    }
    try p.expect(.dedent);
}

fn parseGroup(p: *P, b: *Builder) ParseError!void {
    switch (p.cur().kind) {
        .or_group => {
            _ = p.advance();
            try b.startGroup(.or_group);
            defer b.endGroup();
            try parseGroupSpec(p, b);
        },
        .alternative => {
            _ = p.advance();
            try b.startGroup(.xor_group);
            defer b.endGroup();
            try parseGroupSpec(p, b);
        },
        .mandatory => {
            _ = p.advance();
            try b.startGroup(.mandatory_children);
            defer b.endGroup();
            try parseGroupSpec(p, b);
        },
        .optional => {
            _ = p.advance();
            try b.startGroup(.optional_children);
            defer b.endGroup();
            try parseGroupSpec(p, b);
        },
        .cardinality_lit => {
            // Cardinality groups are never wrapped with startGroup/endGroup
            // (see builder.zig's doc comment): their members become plain
            // optional children of the enclosing feature, with no clause
            // anywhere enforcing the [i..j] bound -- see
            // docs/non_boolean_support.md, Tier 1.
            _ = p.advance();
            b.cardinality_group_count += 1;
            try parseGroupSpec(p, b);
        },
        else => return ParseError.UnexpectedToken,
    }
}

pub const ConstraintInfo = struct {
    node: ?*constraint.Node,
    text_line: u32,
    /// Raw source text of the constraint, matching what
    /// LarkFeatureExtractor/AntlrFeatureExtractor capture into
    /// boolean_constraints/arithmetic_constraints (reconstructed from
    /// token text there too, via Lark's tree-join / ANTLR's .getText()).
    text: []const u8,
    saw_dot: bool,
    saw_comparison: bool,
    saw_bool_op: bool,
};

pub const ParseResult = struct {
    builder: Builder,
    constraints: []ConstraintInfo,
};

/// includes: INCLUDE_KEY NEWLINE INDENT include_line* DEDENT
/// include_line: language_level NEWLINE
/// We don't need language-level semantics for CNF, just correct skipping.
fn parseIncludes(p: *P) ParseError!void {
    try p.expect(.include_key);
    try p.expect(.newline);
    try p.expect(.indent);
    while (!p.check(.dedent)) {
        // language_level: major_level (DOT (minor_level | MUL))?
        _ = p.advance(); // major_level keyword
        if (p.check(.dot)) {
            _ = p.advance();
            _ = p.advance(); // minor_level keyword or '*'
        }
        try p.expect(.newline);
    }
    try p.expect(.dedent);
}

/// imports: IMPORTS_KEY NEWLINE INDENT import_line* DEDENT
/// import_line: reference (AS_KEY reference)? NEWLINE
fn parseImports(p: *P) ParseError!void {
    try p.expect(.imports_key);
    try p.expect(.newline);
    try p.expect(.indent);
    while (!p.check(.dedent)) {
        _ = try parseReferenceName(p);
        if (p.check(.as_key)) {
            _ = p.advance();
            _ = try parseReferenceName(p);
        }
        try p.expect(.newline);
    }
    try p.expect(.dedent);
}

pub fn parseModel(alloc: Allocator, tokens: []const Token) ParseError!ParseResult {
    var p = P{ .alloc = alloc, .tokens = tokens };
    var b = Builder.init(alloc);

    if (p.check(.namespace_key)) {
        _ = p.advance();
        _ = try parseReferenceName(&p);
        p.skipNewlineIfPresent();
    }
    if (p.check(.include_key)) {
        try parseIncludes(&p);
        p.skipNewlineIfPresent();
    }
    if (p.check(.imports_key)) {
        try parseImports(&p);
        p.skipNewlineIfPresent();
    }
    if (p.check(.features_key)) {
        _ = p.advance();
        try p.expect(.newline);
        try p.expect(.indent);
        try parseFeature(&p, &b);
        try p.expect(.dedent);
        p.skipNewlineIfPresent();
    }

    var constraints = std.ArrayList(ConstraintInfo).empty;
    if (p.check(.constraints_key)) {
        _ = p.advance();
        try p.expect(.newline);
        try p.expect(.indent);
        while (!p.check(.dedent)) {
            const line = p.cur().line;
            const start_pos = p.pos;
            const parsed = try constraint.parseConstraint(alloc, p.tokens, p.pos);
            p.pos = parsed.end_pos;
            const text = spanText(p.tokens[start_pos], p.tokens[parsed.end_pos - 1]);
            try p.expect(.newline);
            try constraints.append(alloc, .{
                .node = parsed.node,
                .text_line = line,
                .text = text,
                .saw_dot = parsed.saw_dot,
                .saw_comparison = parsed.saw_comparison,
                .saw_bool_op = parsed.saw_bool_op,
            });
        }
        try p.expect(.dedent);
    }

    return .{ .builder = b, .constraints = try constraints.toOwnedSlice(alloc) };
}

const lexer = @import("lexer.zig");

test "feature type and attributes are captured" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root {abstract, weight 3, "quoted key" 'val'}
        \\        optional
        \\            String Label {default "hello", tags [1, 2]}
        \\
        \\constraints
        \\    Root => Label
        \\
    ;
    const tokens = try lexer.tokenize(alloc, src);
    const result = try parseModel(alloc, tokens);

    try std.testing.expectEqualStrings("Root", result.builder.root.?);
    try std.testing.expectEqual(@as(usize, 2), result.builder.ordered_features.items.len);
    try std.testing.expectEqualStrings("Root", result.builder.ordered_features.items[0]);
    try std.testing.expectEqualStrings("Label", result.builder.ordered_features.items[1]);

    const root_info = result.builder.hierarchy.get("Root").?;
    try std.testing.expect(root_info.feature_type == null);
    // "abstract" is a bare key with no value -- not recorded, matching
    // LarkFeatureExtractor/AntlrFeatureExtractor.
    try std.testing.expectEqual(@as(usize, 2), root_info.attributes.items.len);
    try std.testing.expectEqualStrings("weight", root_info.attributes.items[0].key);
    try std.testing.expectEqualStrings("3", root_info.attributes.items[0].value);
    try std.testing.expectEqualStrings("\"quoted key\"", root_info.attributes.items[1].key);
    try std.testing.expectEqualStrings("'val'", root_info.attributes.items[1].value);

    const label_info = result.builder.hierarchy.get("Label").?;
    try std.testing.expectEqualStrings("String", label_info.feature_type.?);
    try std.testing.expectEqualStrings("Root", label_info.parent.?);
    try std.testing.expectEqual(@as(usize, 2), label_info.attributes.items.len);
    try std.testing.expectEqualStrings("default", label_info.attributes.items[0].key);
    try std.testing.expectEqualStrings("\"hello\"", label_info.attributes.items[0].value);
    try std.testing.expectEqualStrings("tags", label_info.attributes.items[1].key);
    try std.testing.expectEqualStrings("[1, 2]", label_info.attributes.items[1].value);

    try std.testing.expectEqual(@as(usize, 1), result.builder.typed_feature_count);
    try std.testing.expectEqual(@as(usize, 2), result.builder.attributed_feature_count);
    try std.testing.expectEqual(@as(usize, 0), result.builder.cardinality_group_count);
    try std.testing.expectEqual(@as(usize, 0), result.builder.cardinality_feature_count);
    try std.testing.expectEqual(@as(usize, 0), result.builder.constraint_attribute_count);

    try std.testing.expectEqual(@as(usize, 1), result.constraints.len);
    try std.testing.expectEqualStrings("Root => Label", result.constraints[0].text);
}

test "constraint attribute bodies are skipped, not extracted" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root {constraint A => B, constraints [A, B]}
        \\        optional
        \\            A
        \\            B
        \\
    ;
    const tokens = try lexer.tokenize(alloc, src);
    const result = try parseModel(alloc, tokens);

    const root_info = result.builder.hierarchy.get("Root").?;
    try std.testing.expectEqual(@as(usize, 0), root_info.attributes.items.len);
    try std.testing.expectEqual(@as(usize, 0), result.constraints.len);
    try std.testing.expectEqual(@as(usize, 2), result.builder.constraint_attribute_count);
}

test "cardinality counters: group and feature cardinality" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        [1..2]
        \\            A cardinality [1..3]
        \\            B
        \\
    ;
    const tokens = try lexer.tokenize(alloc, src);
    const result = try parseModel(alloc, tokens);

    try std.testing.expectEqual(@as(usize, 1), result.builder.cardinality_group_count);
    try std.testing.expectEqual(@as(usize, 1), result.builder.cardinality_feature_count);
    try std.testing.expectEqual(@as(usize, 0), result.builder.typed_feature_count);
    try std.testing.expectEqual(@as(usize, 0), result.builder.attributed_feature_count);
}

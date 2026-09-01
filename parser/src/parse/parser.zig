const std = @import("std");
const Allocator = std.mem.Allocator;
const tok = @import("token");
const Token = tok.Token;
const Kind = tok.Kind;
const builder_mod = @import("builder");
const Builder = builder_mod.Builder;
const constraint = @import("constraint");

pub const ParseError = error{ UnexpectedToken, UnexpectedEnd, NoFeatures } || Allocator.Error || constraint.ParseError;

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

/// Parses a `cardinality_lit` token's raw text -- `"[n]"`, `"[n..m]"`, or
/// `"[n..*]"` (brackets included, per `lexer.zig:scanCardinality`) -- into
/// a `builder_mod.CardinalityRange`. Malformed input (should be
/// unreachable, since the lexer only emits this token for text matching
/// its own regex) falls back to `{0, 0}` rather than erroring, since this
/// is metadata for an optional conversion, not load-bearing for parsing.
fn parseCardinalityRange(text: []const u8) builder_mod.CardinalityRange {
    if (text.len < 2) return .{ .min = 0, .max = 0 };
    const inner = text[1 .. text.len - 1];
    if (std.mem.indexOf(u8, inner, "..")) |dot_idx| {
        const min = std.fmt.parseInt(u32, inner[0..dot_idx], 10) catch 0;
        const max_s = inner[dot_idx + 2 ..];
        if (std.mem.eql(u8, max_s, "*")) return .{ .min = min, .max = null };
        const max = std.fmt.parseInt(u32, max_s, 10) catch min;
        return .{ .min = min, .max = max };
    }
    const n = std.fmt.parseInt(u32, inner, 10) catch 0;
    return .{ .min = n, .max = n };
}

/// Splits the inner text of a bracketed list (`"[a, b, c]"`, brackets
/// included in `bracketed`) on top-level commas -- i.e. commas not nested
/// inside `()`/`[]`/`{}`, since a single constraint expression can itself
/// contain a comma (e.g. `sum(A, B)`). Trims surrounding whitespace from
/// each item; an empty list (`"[]"`) yields zero items.
fn splitTopLevelCommaList(alloc: Allocator, bracketed: []const u8) ![]const []const u8 {
    const inner = bracketed[1 .. bracketed.len - 1];
    var items = std.ArrayList([]const u8).empty;
    var depth: i32 = 0;
    var start: usize = 0;
    for (inner, 0..) |ch, i| {
        switch (ch) {
            '(', '[', '{' => depth += 1,
            ')', ']', '}' => depth -= 1,
            ',' => if (depth == 0) {
                try items.append(alloc, std.mem.trim(u8, inner[start..i], " \t\r\n"));
                start = i + 1;
            },
            else => {},
        }
    }
    const last = std.mem.trim(u8, inner[start..], " \t\r\n");
    if (last.len > 0) try items.append(alloc, last);
    return items.toOwnedSlice(alloc);
}

/// Re-lexes and parses one feature-local constraint expression (already
/// isolated as raw text by the caller), appending it to
/// `b.feature_local_constraints` on success. Silently does nothing on a
/// lex/parse failure -- this is best-effort extraction for an optional
/// conversion, not something that should fail the whole model parse; the
/// construct is still counted via `constraint_attribute_count` either way.
fn extractFeatureLocalConstraint(p: *P, b: *Builder, feature_name: []const u8, text: []const u8, line: u32) ParseError!void {
    const sub_tokens = lexer.tokenize(p.alloc, text) catch return;
    const parsed = constraint.parseConstraint(p.alloc, sub_tokens, 0) catch return;
    try b.feature_local_constraints.append(p.alloc, .{
        .feature = feature_name,
        .node = parsed.node,
        .full = parsed.full,
        .text = text,
        .text_line = line,
        .saw_dot = parsed.saw_dot,
        .saw_comparison = parsed.saw_comparison,
        .saw_bool_op = parsed.saw_bool_op,
    });
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
            const line = p.cur().line;
            const text = try skipUntilCommaOrRbrace(p);
            b.constraint_attribute_count += 1;
            try extractFeatureLocalConstraint(p, b, feature_name, text, line);
        },
        .constraints_key => {
            _ = p.advance();
            if (p.check(.lbrack)) {
                const line = p.cur().line;
                const text = try skipBalanced(p);
                const items = try splitTopLevelCommaList(p.alloc, text);
                for (items) |item| {
                    try extractFeatureLocalConstraint(p, b, feature_name, item, line);
                }
            }
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
            // anywhere enforcing the [i..j] bound by default -- see
            // README.md#non-boolean-constructs, Tier 1. `--conversion`/
            // `conversion=True` encodes the bound from the
            // `Builder.cardinality_groups` side-channel captured here
            // instead (see capi.zig/uvl2cnf.zig).
            const range = parseCardinalityRange(p.cur().text);
            _ = p.advance();
            b.cardinality_group_count += 1;
            const parent = b.current_feature.?; // groups only ever occur inside a feature
            const before = if (b.hierarchy.getPtr(parent)) |info| info.children.items.len else 0;
            try parseGroupSpec(p, b);
            var cg = builder_mod.CardinalityGroup{ .parent = parent, .range = range };
            if (b.hierarchy.getPtr(parent)) |info| {
                for (info.children.items[before..]) |edge| {
                    try cg.members.append(b.alloc, edge.name);
                }
            }
            try b.cardinality_groups.append(b.alloc, cg);
        },
        else => return ParseError.UnexpectedToken,
    }
}

pub const ConstraintInfo = struct {
    node: ?*constraint.Node,
    /// The complete tree regardless of `node` -- see `constraint.ConstraintParse.full`.
    full: *constraint.Node,
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
                .full = parsed.full,
                .text_line = line,
                .text = text,
                .saw_dot = parsed.saw_dot,
                .saw_comparison = parsed.saw_comparison,
                .saw_bool_op = parsed.saw_bool_op,
            });
        }
        try p.expect(.dedent);
    }

    // A valid UVL model has at least one feature (the root); this also
    // rejects non-UVL input that happens not to hit any of the branches
    // above (e.g. a DIMACS or SMT-LIB file) instead of silently returning
    // an empty model.
    if (b.ordered_features.items.len == 0) return ParseError.NoFeatures;

    return .{ .builder = b, .constraints = try constraints.toOwnedSlice(alloc) };
}

const lexer = @import("lexer");

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

    // Real extraction (Phase 1: uvl2cnf --conversion) happens regardless
    // of the flag -- only *using* it for CNF generation is conditional.
    // "constraint A => B" is one FeatureLocalConstraint; "constraints
    // [A, B]" is two bare-literal ones (each just a reference, not a
    // real boolean expression, so both parse to a plain `.lit` node).
    try std.testing.expectEqual(@as(usize, 3), result.builder.feature_local_constraints.items.len);
    const flc = result.builder.feature_local_constraints.items;
    try std.testing.expectEqualStrings("Root", flc[0].feature);
    try std.testing.expectEqualStrings("A => B", flc[0].text);
    try std.testing.expect(flc[0].node != null);
    try std.testing.expectEqualStrings("A", flc[1].text);
    try std.testing.expectEqualStrings("B", flc[2].text);
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

    try std.testing.expectEqual(@as(usize, 1), result.builder.cardinality_groups.items.len);
    const cg = result.builder.cardinality_groups.items[0];
    try std.testing.expectEqualStrings("Root", cg.parent);
    try std.testing.expectEqual(@as(u32, 1), cg.range.min);
    try std.testing.expectEqual(@as(?u32, 2), cg.range.max);
    try std.testing.expectEqual(@as(usize, 2), cg.members.items.len);
    try std.testing.expectEqualStrings("A", cg.members.items[0]);
    try std.testing.expectEqualStrings("B", cg.members.items[1]);
}

test "cardinality range parsing: bare, range, and unbounded forms" {
    try std.testing.expectEqual(builder_mod.CardinalityRange{ .min = 3, .max = 3 }, parseCardinalityRange("[3]"));
    try std.testing.expectEqual(builder_mod.CardinalityRange{ .min = 1, .max = 3 }, parseCardinalityRange("[1..3]"));
    try std.testing.expectEqual(builder_mod.CardinalityRange{ .min = 2, .max = null }, parseCardinalityRange("[2..*]"));
}

test "splitTopLevelCommaList: nested commas inside a function call are not split" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const items = try splitTopLevelCommaList(alloc, "[sum(A, B) > 3, C]");
    try std.testing.expectEqual(@as(usize, 2), items.len);
    try std.testing.expectEqualStrings("sum(A, B) > 3", items[0]);
    try std.testing.expectEqualStrings("C", items[1]);

    const empty = try splitTopLevelCommaList(alloc, "[]");
    try std.testing.expectEqual(@as(usize, 0), empty.len);
}

test "parseModel rejects a zero-feature model (e.g. non-UVL input)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const tokens = try lexer.tokenize(alloc, "p cnf 1 1\n1 0\n");
    try std.testing.expectError(ParseError.NoFeatures, parseModel(alloc, tokens));
}

test "parseModel accepts a single-feature model" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const tokens = try lexer.tokenize(alloc, "features\n    Root\n");
    const result = try parseModel(alloc, tokens);
    try std.testing.expectEqual(@as(usize, 1), result.builder.ordered_features.items.len);
}

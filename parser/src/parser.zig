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

/// Blindly consumes a balanced `{ ... }` block. Attribute content (value
/// attributes, vectors, nested attributes, constraint attributes) is never
/// used by CNF generation -- mirrors LarkFeatureExtractor, which only ever
/// extracts value_attribute pairs and to_cnf never reads them -- so a
/// grammar-agnostic bracket-depth skip is sufficient and avoids needing a
/// second full expression grammar just to throw the result away.
fn skipAttributes(p: *P) !void {
    try p.expect(.lbrace);
    var depth: i32 = 1;
    while (depth > 0) {
        if (p.check(.eof)) return ParseError.UnexpectedEnd;
        const t = p.advance();
        switch (t.kind) {
            .lparen, .lbrack, .lbrace => depth += 1,
            .rparen, .rbrack, .rbrace => depth -= 1,
            else => {},
        }
    }
}

fn parseFeature(p: *P, b: *Builder) ParseError!void {
    if (isFeatureType(p.cur().kind)) _ = p.advance();

    const name = try parseReferenceName(p);
    try b.startFeature(name);
    defer b.endFeature();

    if (p.check(.cardinality_key)) {
        _ = p.advance();
        try p.expect(.cardinality_lit);
    }
    if (p.check(.lbrace)) try skipAttributes(p);

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
            // optional children of the enclosing feature.
            _ = p.advance();
            try parseGroupSpec(p, b);
        },
        else => return ParseError.UnexpectedToken,
    }
}

pub const ConstraintInfo = struct {
    node: ?*constraint.Node,
    text_line: u32,
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
            const parsed = try constraint.parseConstraint(alloc, p.tokens, p.pos);
            p.pos = parsed.end_pos;
            try p.expect(.newline);
            try constraints.append(alloc, .{
                .node = parsed.node,
                .text_line = line,
                .saw_dot = parsed.saw_dot,
                .saw_comparison = parsed.saw_comparison,
                .saw_bool_op = parsed.saw_bool_op,
            });
        }
        try p.expect(.dedent);
    }

    return .{ .builder = b, .constraints = try constraints.toOwnedSlice(alloc) };
}

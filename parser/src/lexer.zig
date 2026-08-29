const std = @import("std");
const Allocator = std.mem.Allocator;
const tok = @import("token.zig");
const Token = tok.Token;
const Kind = tok.Kind;

pub const LexError = error{
    UnterminatedString,
    UnexpectedChar,
} || Allocator.Error;

fn isDigit(c: u8) bool {
    return c >= '0' and c <= '9';
}

fn isAlphaAscii(c: u8) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z');
}

// Approximates the ID_STRICT continuation charset (ASCII letters/digits/_
// plus a handful of punctuation, plus the handful of accented Latin-1
// letters and section-sign the grammar allows). Any non-ASCII byte is
// accepted as a continuation byte, which is a safe superset for real UVL
// model files (all identifiers we need to round-trip are ASCII).
fn isIdContinue(c: u8) bool {
    return isAlphaAscii(c) or isDigit(c) or switch (c) {
        '_', '#', '%', '?', '\\', '\'', ';' => true,
        else => c >= 0x80,
    };
}

fn indentWidth(spaces: []const u8) u32 {
    var count: u32 = 0;
    for (spaces) |c| {
        if (c == '\t') {
            count += 8 - (count % 8);
        } else {
            count += 1;
        }
    }
    return count;
}

pub const Lexer = struct {
    src: []const u8,
    pos: usize = 0,
    line: u32 = 1,
    opened: i32 = 0,
    indents: std.ArrayList(u32) = .empty,
    tokens: std.ArrayList(Token) = .empty,
    alloc: Allocator,

    fn peek(l: *Lexer) ?u8 {
        if (l.pos >= l.src.len) return null;
        return l.src[l.pos];
    }

    fn peekAt(l: *Lexer, offset: usize) ?u8 {
        const p = l.pos + offset;
        if (p >= l.src.len) return null;
        return l.src[p];
    }

    fn emit(l: *Lexer, kind: Kind, text: []const u8) !void {
        try l.tokens.append(l.alloc, .{ .kind = kind, .text = text, .line = l.line });
    }

    fn isNumberStart(l: *Lexer) bool {
        const c0 = l.peek() orelse return false;
        if (isDigit(c0)) return true;
        if (c0 == '.') return isDigit(l.peekAt(1) orelse return false);
        if (c0 == '-') {
            const c1 = l.peekAt(1) orelse return false;
            if (isDigit(c1)) return true;
            if (c1 == '.') return isDigit(l.peekAt(2) orelse return false);
        }
        return false;
    }

    fn scanNumber(l: *Lexer) !void {
        const start = l.pos;
        if (l.peek() == @as(u8, '-')) l.pos += 1;
        var saw_digits = false;
        while (l.peek()) |c| {
            if (!isDigit(c)) break;
            l.pos += 1;
            saw_digits = true;
        }
        var is_float = false;
        if (l.peek() == @as(u8, '.')) {
            is_float = true;
            l.pos += 1;
            var frac_digits = false;
            while (l.peek()) |c| {
                if (!isDigit(c)) break;
                l.pos += 1;
                frac_digits = true;
            }
            if (!frac_digits) return LexError.UnexpectedChar;
        }
        if (!saw_digits and !is_float) return LexError.UnexpectedChar;
        try l.emit(if (is_float) .float else .integer, l.src[start..l.pos]);
    }

    fn scanQuoted(l: *Lexer) !void {
        const quote = l.peek().?;
        const start = l.pos;
        if (quote == '\'') {
            l.pos += 1;
            while (true) {
                const c = l.peek() orelse return LexError.UnterminatedString;
                if (c == '\r' or c == '\n') return LexError.UnterminatedString;
                l.pos += 1;
                if (c == '\'') break;
            }
            try l.emit(.string_lit, l.src[start..l.pos]);
            return;
        }
        // Double-quoted: could be ID_NOT_STRICT (no dot allowed inside) or
        // STRING (dots allowed). Try the stricter ID_NOT_STRICT reading
        // first; fall back to STRING if a dot appears before the closing
        // quote.
        var p = l.pos + 1;
        var has_dot = false;
        var terminated = false;
        while (p < l.src.len) {
            const c = l.src[p];
            if (c == '"') {
                terminated = true;
                break;
            }
            if (c == '\r' or c == '\n') break;
            if (c == '.') has_dot = true;
            p += 1;
        }
        if (terminated and !has_dot and p > l.pos + 1) {
            l.pos = p + 1;
            try l.emit(.id_not_strict, l.src[start..l.pos]);
            return;
        }
        // STRING: any char except unescaped quote/CR/LF.
        l.pos += 1;
        while (true) {
            const c = l.peek() orelse return LexError.UnterminatedString;
            if (c == '\r' or c == '\n') return LexError.UnterminatedString;
            l.pos += 1;
            if (c == '"') break;
        }
        try l.emit(.string_lit, l.src[start..l.pos]);
    }

    fn scanIdentifier(l: *Lexer) !void {
        const start = l.pos;
        l.pos += 1;
        while (l.peek()) |c| {
            if (!isIdContinue(c)) break;
            l.pos += 1;
        }
        try l.emit(.id_strict, l.src[start..l.pos]);
    }

    fn scanCardinality(l: *Lexer) !bool {
        // /\[[0-9]+(\.\.[0-9]+|\.\.\*)?\]/
        var p = l.pos + 1;
        const digit_start = p;
        while (p < l.src.len and isDigit(l.src[p])) p += 1;
        if (p == digit_start) return false;
        if (p + 1 < l.src.len and l.src[p] == '.' and l.src[p + 1] == '.') {
            var q = p + 2;
            if (q < l.src.len and l.src[q] == '*') {
                q += 1;
            } else {
                const d2 = q;
                while (q < l.src.len and isDigit(l.src[q])) q += 1;
                if (q == d2) return false;
            }
            p = q;
        }
        if (p >= l.src.len or l.src[p] != ']') return false;
        p += 1;
        try l.emit(.cardinality_lit, l.src[l.pos..p]);
        l.pos = p;
        return true;
    }

    fn tryLiteral(l: *Lexer) !bool {
        for (tok.literal_table) |entry| {
            if (l.pos + entry.text.len > l.src.len) continue;
            if (!std.mem.eql(u8, l.src[l.pos .. l.pos + entry.text.len], entry.text)) continue;
            if (entry.alpha) {
                const after = l.peekAt(entry.text.len);
                if (after) |a| {
                    if (isIdContinue(a)) continue; // longer identifier, not this keyword
                }
            }
            const start = l.pos;
            l.pos += entry.text.len;
            switch (entry.kind) {
                .lparen, .lbrack, .lbrace => l.opened += 1,
                .rparen, .rbrack, .rbrace => l.opened -= 1,
                else => {},
            }
            try l.emit(entry.kind, l.src[start..l.pos]);
            return true;
        }
        return false;
    }

    fn skipLineComment(l: *Lexer) void {
        while (l.peek()) |c| {
            if (c == '\r' or c == '\n') break;
            l.pos += 1;
        }
    }

    fn skipBlockComment(l: *Lexer) void {
        // Greedy: match through to the LAST "*/" in the remaining source,
        // matching uvl_lexer.g4's `OPEN_COMMENT .* CLOSE_COMMENT` (ANTLR4's
        // `.*` is greedy by default) and uvl_lark_lexer.py's matching
        // choice -- not the first "*/" encountered. Deliberately not
        // aware of quoted spans either: ANTLR's own generated lexer isn't,
        // since once it commits to the COMMENT rule it matches via that
        // rule's own `.*` against raw characters, never re-entering
        // STRING/ID_NOT_STRICT to recognize a quote boundary partway
        // through -- being smarter here would just be a different kind of
        // mismatch between backends.
        var last_close: ?usize = null;
        var i = l.pos + 2;
        while (i + 1 < l.src.len) : (i += 1) {
            if (l.src[i] == '*' and l.src[i + 1] == '/') last_close = i;
        }
        if (last_close) |lc| {
            for (l.src[l.pos..lc]) |c| {
                if (c == '\n') l.line += 1;
            }
            l.pos = lc + 2;
        } else {
            for (l.src[l.pos..]) |c| {
                if (c == '\n') l.line += 1;
            }
            l.pos = l.src.len; // unterminated: tolerate, consume to EOF
        }
    }

    fn handleNewline(l: *Lexer) !void {
        // Consume the newline sequence itself.
        const c = l.peek().?;
        l.pos += 1;
        if (c == '\r' and l.peek() == @as(u8, '\n')) l.pos += 1;
        l.line += 1;

        if (l.opened > 0) return; // inside brackets: insignificant

        var p = l.pos;
        while (p < l.src.len and (l.src[p] == ' ' or l.src[p] == '\t')) p += 1;
        const spaces = l.src[l.pos..p];

        const blank = p >= l.src.len or l.src[p] == '\r' or l.src[p] == '\n';
        const comment = p + 1 < l.src.len and l.src[p] == '/' and (l.src[p + 1] == '/' or l.src[p + 1] == '*');
        if (blank or comment) {
            l.pos = p; // consume leading whitespace, leave the rest for the next pass
            return;
        }

        l.pos = p; // consume the indentation whitespace
        // Leading blank lines before the very first real token don't
        // separate anything -- grammar's `NEWLINE?` markers are for
        // between sections, not for whatever blank padding precedes the
        // first one, so only emit a NEWLINE once real content exists.
        if (l.tokens.items.len > 0) try l.emit(.newline, "\n");

        const indent = indentWidth(spaces);
        const previous: u32 = if (l.indents.items.len == 0) 0 else l.indents.items[l.indents.items.len - 1];

        if (indent == previous) {
            // nothing to do
        } else if (indent > previous) {
            try l.indents.append(l.alloc, indent);
            try l.emit(.indent, spaces);
        } else {
            while (l.indents.items.len > 0 and l.indents.items[l.indents.items.len - 1] > indent) {
                try l.emit(.dedent, "");
                _ = l.indents.pop();
            }
        }
    }

    fn finish(l: *Lexer) !void {
        if (l.indents.items.len != 0) {
            try l.emit(.newline, "\n");
            while (l.indents.items.len > 0) {
                try l.emit(.dedent, "");
                _ = l.indents.pop();
            }
        }
        try l.emit(.eof, "");
    }
};

pub fn tokenize(alloc: Allocator, src: []const u8) LexError![]Token {
    var l = Lexer{ .src = src, .alloc = alloc };

    while (l.pos < l.src.len) {
        const c = l.src[l.pos];

        if (c == '\r' or c == '\n') {
            try l.handleNewline();
            continue;
        }
        if (c == ' ' or c == '\t') {
            l.pos += 1;
            continue;
        }
        if (c == '/' and l.peekAt(1) == @as(u8, '/')) {
            l.skipLineComment();
            continue;
        }
        if (c == '/' and l.peekAt(1) == @as(u8, '*')) {
            l.skipBlockComment();
            continue;
        }
        if (l.isNumberStart()) {
            try l.scanNumber();
            continue;
        }
        if (c == '[') {
            if (try l.scanCardinality()) continue;
        }
        if (try l.tryLiteral()) continue;
        if (c == '"' or c == '\'') {
            try l.scanQuoted();
            continue;
        }
        if (isAlphaAscii(c) or c == '_' or c >= 0x80) {
            try l.scanIdentifier();
            continue;
        }
        return LexError.UnexpectedChar;
    }

    try l.finish();
    return l.tokens.toOwnedSlice(l.alloc);
}

test "basic tokenize" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const src = "namespace Test\n\nfeatures\n\tRoot\n\t\toptional\n\t\t\tA\n\nconstraints\n\tA => Root\n";
    const toks = try tokenize(alloc, src);
    var kinds = std.ArrayList(Kind).empty;
    for (toks) |t| try kinds.append(alloc, t.kind);
    // Just sanity check a few key structural markers appear correctly.
    try std.testing.expect(std.mem.indexOfScalar(Kind, kinds.items, .indent) != null);
    try std.testing.expect(std.mem.indexOfScalar(Kind, kinds.items, .dedent) != null);
    try std.testing.expectEqual(Kind.eof, kinds.items[kinds.items.len - 1]);
}

test "blank line preserves indent stack" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const src = "A\n\tB\n\t\tC\n\t\tD\n\n\t\tE\n";
    const toks = try tokenize(alloc, src);
    var d_idx: ?usize = null;
    var e_idx: ?usize = null;
    for (toks, 0..) |t, i| {
        if (std.mem.eql(u8, t.text, "D")) d_idx = i;
        if (std.mem.eql(u8, t.text, "E")) e_idx = i;
    }
    const between = toks[d_idx.? + 1 .. e_idx.?];
    for (between) |t| {
        try std.testing.expect(t.kind != .indent and t.kind != .dedent);
    }
}

test "cardinality literal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const src = "[2..3]";
    const toks = try tokenize(alloc, src);
    try std.testing.expectEqual(Kind.cardinality_lit, toks[0].kind);
    try std.testing.expectEqualStrings("[2..3]", toks[0].text);
}

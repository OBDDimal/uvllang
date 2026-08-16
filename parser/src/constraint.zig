const std = @import("std");
const Allocator = std.mem.Allocator;
const tok = @import("token.zig");
const Token = tok.Token;
const Kind = tok.Kind;

/// Boolean-constraint AST. Mirrors the shape of the tuple AST that
/// uvllang/main.py's `_parse_boolean_expr` builds (`LIT`/`NOT`/`AND`/`OR`/
/// `IMPLIES`/`EQUIVALENCE`), so `nnf`/`distribute`/`extractClauses` below
/// are a direct, typed port of `_to_nnf`/`_distribute`/`_extract_clauses`.
/// `invalid` stands in for anything the CNF pipeline can't encode
/// (a comparison, or a plain arithmetic atom) -- reaching it during clause
/// generation is a bug, since such constraints are filtered out earlier by
/// checking `saw_comparison`.
pub const Node = union(enum) {
    lit: []const u8,
    not: *Node,
    and_: [2]*Node,
    or_: [2]*Node,
    implies: [2]*Node,
    equiv: [2]*Node,
    invalid: void,
};

fn makeLit(alloc: Allocator, name: []const u8) !*Node {
    const n = try alloc.create(Node);
    n.* = .{ .lit = name };
    return n;
}

fn makeUnary(alloc: Allocator, inner: *Node) !*Node {
    const n = try alloc.create(Node);
    n.* = .{ .not = inner };
    return n;
}

fn makeBin(alloc: Allocator, comptime tag: std.meta.Tag(Node), a: *Node, b: *Node) !*Node {
    const n = try alloc.create(Node);
    n.* = @unionInit(Node, @tagName(tag), .{ a, b });
    return n;
}

fn makeInvalid(alloc: Allocator) !*Node {
    const n = try alloc.create(Node);
    n.* = .invalid;
    return n;
}

pub const ParseError = error{ UnexpectedToken, UnexpectedEnd } || Allocator.Error;

const Ref = struct { name: []const u8, dotted: bool };

const ParseCtx = struct {
    alloc: Allocator,
    tokens: []const Token,
    pos: usize,
    saw_comparison: bool = false,
    saw_dot: bool = false,
    saw_bool_op: bool = false,

    fn cur(c: *ParseCtx) Token {
        return c.tokens[c.pos];
    }

    fn advance(c: *ParseCtx) Token {
        const t = c.tokens[c.pos];
        if (c.pos + 1 < c.tokens.len) c.pos += 1;
        return t;
    }

    fn check(c: *ParseCtx, k: Kind) bool {
        return c.cur().kind == k;
    }

    fn expect(c: *ParseCtx, k: Kind) !void {
        if (!c.check(k)) return ParseError.UnexpectedToken;
        _ = c.advance();
    }
};

fn isComparisonOp(k: Kind) bool {
    return switch (k) {
        .eq, .lt, .le, .gt, .ge, .ne => true,
        else => false,
    };
}

fn isReferenceStart(k: Kind) bool {
    return k == .id_strict or k == .id_not_strict;
}

fn parseReference(c: *ParseCtx) !Ref {
    if (!isReferenceStart(c.cur().kind)) return ParseError.UnexpectedToken;
    var name = std.ArrayList(u8).empty;
    try name.appendSlice(c.alloc, c.advance().text);
    var dotted = false;
    while (c.check(.dot)) {
        dotted = true;
        _ = c.advance();
        try name.appendSlice(c.alloc, ".");
        if (!isReferenceStart(c.cur().kind)) return ParseError.UnexpectedToken;
        try name.appendSlice(c.alloc, c.advance().text);
    }
    return .{ .name = try name.toOwnedSlice(c.alloc), .dotted = dotted };
}

fn parseAggregateArgs(c: *ParseCtx) !void {
    try c.expect(.lparen);
    _ = try parseReference(c);
    if (c.check(.comma)) {
        _ = c.advance();
        _ = try parseReference(c);
    }
    try c.expect(.rparen);
}

/// Parses one comp_primary. Sets `complex` whenever the atom isn't a bare
/// reference (float/int/string/aggregate call/parenthesized sub-expr), and
/// fills `single` with the reference when it is one.
fn parseCompPrimary(c: *ParseCtx, complex: *bool, single: *?Ref) ParseError!void {
    switch (c.cur().kind) {
        .float, .integer, .string_lit => {
            _ = c.advance();
            complex.* = true;
            single.* = null;
        },
        .sum_key, .avg_key, .len_key, .floor_key, .ceil_key => {
            _ = c.advance();
            try parseAggregateArgs(c);
            complex.* = true;
            single.* = null;
        },
        .lparen => {
            _ = c.advance();
            var inner_complex = false;
            var inner_single: ?Ref = null;
            try parseCompExpr(c, &inner_complex, &inner_single);
            try c.expect(.rparen);
            complex.* = true; // parenthesized, never a bare literal
            single.* = null;
        },
        else => {
            if (!isReferenceStart(c.cur().kind)) return ParseError.UnexpectedToken;
            const r = try parseReference(c);
            single.* = r;
        },
    }
}

fn parseCompMultiplicative(c: *ParseCtx, complex: *bool, single: *?Ref) ParseError!void {
    try parseCompPrimary(c, complex, single);
    while (c.check(.mul) or c.check(.div)) {
        _ = c.advance();
        var rc = false;
        var rs: ?Ref = null;
        try parseCompPrimary(c, &rc, &rs);
        complex.* = true;
        single.* = null;
    }
}

fn parseCompExpr(c: *ParseCtx, complex: *bool, single: *?Ref) ParseError!void {
    try parseCompMultiplicative(c, complex, single);
    while (c.check(.add) or c.check(.sub)) {
        _ = c.advance();
        var rc = false;
        var rs: ?Ref = null;
        try parseCompMultiplicative(c, &rc, &rs);
        complex.* = true;
        single.* = null;
    }
}

fn parseAtom(c: *ParseCtx) ParseError!*Node {
    if (c.check(.lparen)) {
        _ = c.advance();
        const inner = try parseEquivalence(c);
        try c.expect(.rparen);
        return inner;
    }

    var complex = false;
    var single: ?Ref = null;
    try parseCompExpr(c, &complex, &single);

    if (isComparisonOp(c.cur().kind)) {
        _ = c.advance();
        var rc = false;
        var rs: ?Ref = null;
        try parseCompExpr(c, &rc, &rs);
        c.saw_comparison = true;
        return makeInvalid(c.alloc);
    }

    if (complex or single == null) {
        c.saw_comparison = true;
        return makeInvalid(c.alloc);
    }

    if (single.?.dotted) c.saw_dot = true;
    return makeLit(c.alloc, single.?.name);
}

fn parseNot(c: *ParseCtx) ParseError!*Node {
    if (c.check(.not)) {
        _ = c.advance();
        const inner = try parseNot(c);
        return makeUnary(c.alloc, inner);
    }
    return parseAtom(c);
}

fn parseAnd(c: *ParseCtx) ParseError!*Node {
    var left = try parseNot(c);
    while (c.check(.amp)) {
        _ = c.advance();
        const right = try parseNot(c);
        left = try makeBin(c.alloc, .and_, left, right);
    }
    return left;
}

fn parseOr(c: *ParseCtx) ParseError!*Node {
    var left = try parseAnd(c);
    while (c.check(.pipe)) {
        _ = c.advance();
        const right = try parseAnd(c);
        left = try makeBin(c.alloc, .or_, left, right);
    }
    return left;
}

fn parseImplication(c: *ParseCtx) ParseError!*Node {
    var left = try parseOr(c);
    while (c.check(.implication)) {
        _ = c.advance();
        c.saw_bool_op = true;
        const right = try parseOr(c);
        left = try makeBin(c.alloc, .implies, left, right);
    }
    return left;
}

fn parseEquivalence(c: *ParseCtx) ParseError!*Node {
    var left = try parseImplication(c);
    while (c.check(.equivalence)) {
        _ = c.advance();
        c.saw_bool_op = true;
        const right = try parseImplication(c);
        left = try makeBin(c.alloc, .equiv, left, right);
    }
    return left;
}

pub const ConstraintParse = struct {
    node: ?*Node,
    saw_dot: bool,
    saw_comparison: bool,
    saw_bool_op: bool,
    end_pos: usize,
};

/// Parses one constraint expression starting at `tokens[start]`, stopping
/// as soon as the grammar cascade bottoms out (a NEWLINE token never
/// matches any continuation, so it's fine to hand this the rest of the
/// token stream rather than a pre-sliced line). `node` is null whenever the
/// constraint should be dropped from the CNF -- either it touches an
/// attribute reference (a dotted literal) or a numeric comparison, matching
/// the classification uvllang/main.py's `_constraints_to_cnf` does on the
/// reconstructed constraint text.
pub fn parseConstraint(alloc: Allocator, tokens: []const Token, start: usize) ParseError!ConstraintParse {
    var c = ParseCtx{ .alloc = alloc, .tokens = tokens, .pos = start };
    const node = try parseEquivalence(&c);
    const skip = c.saw_dot or c.saw_comparison;
    return .{
        .node = if (skip) null else node,
        .saw_dot = c.saw_dot,
        .saw_comparison = c.saw_comparison,
        .saw_bool_op = c.saw_bool_op,
        .end_pos = c.pos,
    };
}

pub const ClauseError = error{UnknownFeature} || Allocator.Error;

fn nnf(alloc: Allocator, n: *Node, negate: bool) ClauseError!*Node {
    switch (n.*) {
        .lit => {
            if (!negate) return n;
            return makeUnary(alloc, n);
        },
        .not => |inner| return nnf(alloc, inner, !negate),
        .and_ => |ab| {
            if (!negate) return makeBin(alloc, .and_, try nnf(alloc, ab[0], false), try nnf(alloc, ab[1], false));
            return makeBin(alloc, .or_, try nnf(alloc, ab[0], true), try nnf(alloc, ab[1], true));
        },
        .or_ => |ab| {
            if (!negate) return makeBin(alloc, .or_, try nnf(alloc, ab[0], false), try nnf(alloc, ab[1], false));
            return makeBin(alloc, .and_, try nnf(alloc, ab[0], true), try nnf(alloc, ab[1], true));
        },
        .implies => |ab| {
            if (!negate) return makeBin(alloc, .or_, try nnf(alloc, ab[0], true), try nnf(alloc, ab[1], false));
            return makeBin(alloc, .and_, try nnf(alloc, ab[0], false), try nnf(alloc, ab[1], true));
        },
        .equiv => |ab| {
            var imp1 = Node{ .implies = .{ ab[0], ab[1] } };
            var imp2 = Node{ .implies = .{ ab[1], ab[0] } };
            var both = Node{ .and_ = .{ &imp1, &imp2 } };
            return nnf(alloc, &both, negate);
        },
        .invalid => return ClauseError.UnknownFeature,
    }
}

// ---- Subsumption-pruned CNF construction ----
//
// Converts an NNF tree to CNF by combining OR/AND directly into clause
// lists, pruning subsumed clauses as it goes rather than materializing a
// full (possibly redundant) cross product first and cleaning up after.
// A clause A subsumes clause B when every literal of A also appears in B:
// since A must be satisfied on its own, and B contains everything A does
// plus more, B is automatically satisfied too and adds no constraint of
// its own -- dropping it changes nothing about the solution space.
//
// This matters because AND already decomposes into one clause per literal
// before any OR-combination happens, so when a literal is common to many
// disjuncts (real-world Kconfig-derived constraints are often shaped like
// a big OR of AND-conjunctions all sharing a handful of enabling literals,
// e.g. `"MEDIA_SUPPORT"` appearing in nearly every conjunct of a ~20-way
// OR), some pair of disjuncts combines that literal with itself and
// produces it as a bare unit clause almost immediately. Once that unit
// clause is kept, every longer candidate containing the same literal is
// subsumed by it and gets dropped before it can combine further --
// collapsing what would otherwise be an exponential cross product. It's
// still an exact CNF over the same variable set (no Tseitin-style
// auxiliary variables): subsumption only removes clauses that were
// already logically implied by another kept clause.
//
// This used to run only as a fallback after an unguarded, unpruned
// distribute -- but that ordering was backwards: pruning is a strict
// improvement (it can only produce the same clause set or a smaller
// logically-equivalent one, never a larger one), so preferring the
// unpruned path by default meant most constraints shipped needlessly
// bloated CNF while only the pathological ones got the better output.
// This is now the only construction path.

pub const CnfError = ClauseError || error{TooComplex};

fn cloneClause(alloc: Allocator, lits: []const i32) ![]i32 {
    const out = try alloc.dupe(i32, lits);
    std.mem.sort(i32, out, {}, std.sort.asc(i32));
    return out;
}

/// Union of two sorted clauses, or null if the result would be
/// tautological (contains both a literal and its negation).
fn unionClause(alloc: Allocator, a: []const i32, b: []const i32) !?[]i32 {
    var set = std.AutoHashMap(i32, void).init(alloc);
    defer set.deinit();
    for (a) |l| try set.put(l, {});
    for (b) |l| try set.put(l, {});

    var it = set.keyIterator();
    while (it.next()) |k| {
        if (set.contains(-k.*)) return null;
    }

    const out = try alloc.alloc(i32, set.count());
    var i: usize = 0;
    var it2 = set.keyIterator();
    while (it2.next()) |k| {
        out[i] = k.*;
        i += 1;
    }
    std.mem.sort(i32, out, {}, std.sort.asc(i32));
    return out;
}

/// True if every literal in `small` also appears in `big` (both sorted
/// ascending) -- i.e. `small` subsumes `big`.
fn subsumes(small: []const i32, big: []const i32) bool {
    if (small.len > big.len) return false;
    var i: usize = 0;
    var j: usize = 0;
    while (i < small.len and j < big.len) {
        if (small[i] == big[j]) {
            i += 1;
            j += 1;
        } else if (small[i] > big[j]) {
            j += 1;
        } else {
            return false;
        }
    }
    return i == small.len;
}

fn addWithSubsumption(alloc: Allocator, kept: *std.ArrayList([]i32), candidate: []i32) !void {
    for (kept.items) |k| {
        if (subsumes(k, candidate)) return; // candidate adds nothing new
    }
    var i: usize = 0;
    while (i < kept.items.len) {
        if (subsumes(candidate, kept.items[i])) {
            _ = kept.swapRemove(i);
        } else {
            i += 1;
        }
    }
    try kept.append(alloc, candidate);
}

/// `pair_budget` bounds the total number of candidate-clause combinations
/// examined across the whole constraint (not just one OR node), so a
/// formula that genuinely has no exploitable subsumption structure still
/// fails fast instead of hanging -- generateClauses treats that as "give
/// up on this one constraint", the same graceful degradation already used
/// for attribute-reference and comparison constraints.
fn buildCnf(alloc: Allocator, features2ids: *const std.StringHashMap(i32), n: *Node, pair_budget: *i64) CnfError![][]i32 {
    switch (n.*) {
        .lit => |name| {
            const id = features2ids.get(name) orelse return ClauseError.UnknownFeature;
            var out = std.ArrayList([]i32).empty;
            try out.append(alloc, try cloneClause(alloc, &[_]i32{id}));
            return out.toOwnedSlice(alloc);
        },
        .not => |inner| {
            switch (inner.*) {
                .lit => |name| {
                    const id = features2ids.get(name) orelse return ClauseError.UnknownFeature;
                    var out = std.ArrayList([]i32).empty;
                    try out.append(alloc, try cloneClause(alloc, &[_]i32{-id}));
                    return out.toOwnedSlice(alloc);
                },
                else => return ClauseError.UnknownFeature,
            }
        },
        .and_ => |ab| {
            const a = try buildCnf(alloc, features2ids, ab[0], pair_budget);
            const b = try buildCnf(alloc, features2ids, ab[1], pair_budget);
            var kept = std.ArrayList([]i32).empty;
            for (a) |c| try addWithSubsumption(alloc, &kept, c);
            for (b) |c| try addWithSubsumption(alloc, &kept, c);
            return kept.toOwnedSlice(alloc);
        },
        .or_ => |ab| {
            const a = try buildCnf(alloc, features2ids, ab[0], pair_budget);
            const b = try buildCnf(alloc, features2ids, ab[1], pair_budget);
            var kept = std.ArrayList([]i32).empty;
            for (a) |ca| {
                for (b) |cb| {
                    pair_budget.* -= 1;
                    if (pair_budget.* < 0) return CnfError.TooComplex;
                    const u = (try unionClause(alloc, ca, cb)) orelse continue;
                    try addWithSubsumption(alloc, &kept, u);
                }
            }
            return kept.toOwnedSlice(alloc);
        },
        .invalid => return ClauseError.UnknownFeature,
        .implies, .equiv => unreachable, // n is already NNF'd
    }
}

/// Direct port of UVL._to_cnf's overall shape (NNF, then CNF, then
/// literal resolution) -- see the module doc comment above for why the
/// distribute step itself is subsumption-pruned rather than a plain,
/// unguarded pairwise distribute.
pub fn generateClauses(alloc: Allocator, features2ids: *const std.StringHashMap(i32), root: *Node) CnfError![][]i32 {
    const in_nnf = try nnf(alloc, root, false);
    var pair_budget: i64 = 5_000_000;
    return buildCnf(alloc, features2ids, in_nnf, &pair_budget);
}

test "A => B produces a single binary clause" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const toks = [_]Token{
        .{ .kind = .id_strict, .text = "A", .line = 1 },
        .{ .kind = .implication, .text = "=>", .line = 1 },
        .{ .kind = .id_strict, .text = "B", .line = 1 },
        .{ .kind = .eof, .text = "", .line = 1 },
    };
    const parsed = try parseConstraint(alloc, &toks, 0);
    try std.testing.expect(parsed.node != null);

    var ids = std.StringHashMap(i32).init(alloc);
    try ids.put("A", 1);
    try ids.put("B", 2);

    const clauses = try generateClauses(alloc, &ids, parsed.node.?);
    try std.testing.expectEqual(@as(usize, 1), clauses.len);
    try std.testing.expectEqual(@as(i32, -1), clauses[0][0]);
    try std.testing.expectEqual(@as(i32, 2), clauses[0][1]);
}

test "dotted attribute reference is skipped" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const toks = [_]Token{
        .{ .kind = .id_strict, .text = "A", .line = 1 },
        .{ .kind = .dot, .text = ".", .line = 1 },
        .{ .kind = .id_strict, .text = "attr", .line = 1 },
        .{ .kind = .eof, .text = "", .line = 1 },
    };
    const parsed = try parseConstraint(alloc, &toks, 0);
    try std.testing.expect(parsed.node == null);
    try std.testing.expect(parsed.saw_dot);
}

test "comparison is skipped" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const toks = [_]Token{
        .{ .kind = .id_strict, .text = "A", .line = 1 },
        .{ .kind = .gt, .text = ">", .line = 1 },
        .{ .kind = .integer, .text = "3", .line = 1 },
        .{ .kind = .eof, .text = "", .line = 1 },
    };
    const parsed = try parseConstraint(alloc, &toks, 0);
    try std.testing.expect(parsed.node == null);
    try std.testing.expect(parsed.saw_comparison);
}

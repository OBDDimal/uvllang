const std = @import("std");
const Allocator = std.mem.Allocator;
const tok = @import("token");
const Token = tok.Token;
const Kind = tok.Kind;

/// Boolean-constraint AST. `nnf`/`distribute`/`extractClauses` below
/// convert it to CNF via negation normal form and distribution of `or`
/// over `and`. `invalid` stands in for anything the CNF pipeline can't
/// encode (a comparison, or a plain arithmetic atom) -- reaching it during
/// clause generation is a bug, since such constraints are filtered out
/// earlier by checking `saw_comparison`.
pub const Node = union(enum) {
    lit: []const u8,
    not: *Node,
    and_: [2]*Node,
    or_: [2]*Node,
    implies: [2]*Node,
    equiv: [2]*Node,
    /// A numeric/string comparison or a bare non-reference arithmetic atom
    /// (e.g. `sum(Power)` alone, with no comparison operator) -- an atom
    /// that isn't Boolean-encodable. `generateClauses` never sees one of
    /// these in practice: `parseConstraint` nulls out `.node` (though not
    /// `.full`, see `ConstraintParse`) whenever `saw_comparison` is set,
    /// which is always set alongside every `.cmp` node this parser ever
    /// produces.
    cmp: *Cmp,
    invalid: void,
};

pub const CmpOp = enum { eq, lt, le, gt, ge, ne };

pub const Cmp = struct {
    op: CmpOp,
    lhs: *ArithNode,
    rhs: *ArithNode,
};

pub const AggFunc = enum { sum, avg, len, floor, ceil };

/// `sum`/`avg`/`floor`/`ceil` accept either a bare attribute-name
/// reference (`sum(Power)`, `scope = null`) or a feature-scoped one
/// (`sum(SomeFeature, Power)`, aggregating only over `SomeFeature` and its
/// descendants -- `scope = "SomeFeature"`), per the grammar's optional
/// leading `(reference COMMA)?`. `len` is always the 1-arg form in
/// practice (a string feature/attribute reference), but is parsed the
/// same way -- the grammar doesn't distinguish arity by function name and
/// neither does this parser.
pub const Aggregate = struct {
    func: AggFunc,
    scope: ?[]const u8,
    arg: []const u8,
};

/// Arithmetic-level expression tree. `num`/`str` keep the raw source text
/// of the literal (matching `AttributeEntry.value`'s convention elsewhere
/// in this codebase) rather than a typed/parsed value -- avoids float
/// round-tripping issues and keeps quote style intact for `str`. `ref` is
/// a feature or `feature.attribute` reference name (dotted iff it
/// contains a literal `.`, since `parseReference` is the only producer of
/// dotted names and always builds them by concatenating with `"."`).
pub const ArithNode = union(enum) {
    num: []const u8,
    str: []const u8,
    ref: []const u8,
    add: [2]*ArithNode,
    sub: [2]*ArithNode,
    mul: [2]*ArithNode,
    div: [2]*ArithNode,
    aggregate: Aggregate,
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

fn makeCmp(alloc: Allocator, op: CmpOp, lhs: *ArithNode, rhs: *ArithNode) !*Node {
    const cmp = try alloc.create(Cmp);
    cmp.* = .{ .op = op, .lhs = lhs, .rhs = rhs };
    const n = try alloc.create(Node);
    n.* = .{ .cmp = cmp };
    return n;
}

fn makeArithLeaf(alloc: Allocator, comptime tag: std.meta.Tag(ArithNode), text: []const u8) !*ArithNode {
    const n = try alloc.create(ArithNode);
    n.* = @unionInit(ArithNode, @tagName(tag), text);
    return n;
}

fn makeArithBin(alloc: Allocator, comptime tag: std.meta.Tag(ArithNode), a: *ArithNode, b: *ArithNode) !*ArithNode {
    const n = try alloc.create(ArithNode);
    n.* = @unionInit(ArithNode, @tagName(tag), .{ a, b });
    return n;
}

fn asBareRef(node: *ArithNode) ?[]const u8 {
    return switch (node.*) {
        .ref => |name| name,
        else => null,
    };
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

fn aggFuncFor(k: Kind) AggFunc {
    return switch (k) {
        .sum_key => .sum,
        .avg_key => .avg,
        .len_key => .len,
        .floor_key => .floor,
        .ceil_key => .ceil,
        else => unreachable,
    };
}

fn cmpOpFor(k: Kind) CmpOp {
    return switch (k) {
        .eq => .eq,
        .lt => .lt,
        .le => .le,
        .gt => .gt,
        .ge => .ge,
        .ne => .ne,
        else => unreachable,
    };
}

/// `AGG_KEY LPAREN reference (COMMA reference)? RPAREN` -- see
/// `Aggregate`'s doc comment for the one-vs-two-arg meaning.
fn parseAggregateArgs(c: *ParseCtx, func: AggFunc) ParseError!*ArithNode {
    try c.expect(.lparen);
    const first = try parseReference(c);
    var scope: ?[]const u8 = null;
    var arg = first.name;
    if (c.check(.comma)) {
        _ = c.advance();
        const second = try parseReference(c);
        scope = first.name;
        arg = second.name;
    }
    try c.expect(.rparen);
    const n = try c.alloc.create(ArithNode);
    n.* = .{ .aggregate = .{ .func = func, .scope = scope, .arg = arg } };
    return n;
}

/// Parses one comp_primary into a real arithmetic-expression node: a
/// numeric/string literal, an aggregate call, a parenthesized
/// sub-expression, or a bare feature/attribute reference.
fn parseCompPrimary(c: *ParseCtx) ParseError!*ArithNode {
    switch (c.cur().kind) {
        .float => return makeArithLeaf(c.alloc, .num, c.advance().text),
        .integer => return makeArithLeaf(c.alloc, .num, c.advance().text),
        .string_lit => return makeArithLeaf(c.alloc, .str, c.advance().text),
        .sum_key, .avg_key, .len_key, .floor_key, .ceil_key => {
            const func = aggFuncFor(c.cur().kind);
            _ = c.advance();
            return parseAggregateArgs(c, func);
        },
        .lparen => {
            _ = c.advance();
            const inner = try parseCompExpr(c);
            try c.expect(.rparen);
            return inner;
        },
        else => {
            if (!isReferenceStart(c.cur().kind)) return ParseError.UnexpectedToken;
            const r = try parseReference(c);
            return makeArithLeaf(c.alloc, .ref, r.name);
        },
    }
}

fn parseCompMultiplicative(c: *ParseCtx) ParseError!*ArithNode {
    var left = try parseCompPrimary(c);
    while (c.check(.mul) or c.check(.div)) {
        const is_mul = c.check(.mul);
        _ = c.advance();
        const right = try parseCompPrimary(c);
        left = if (is_mul)
            try makeArithBin(c.alloc, .mul, left, right)
        else
            try makeArithBin(c.alloc, .div, left, right);
    }
    return left;
}

fn parseCompExpr(c: *ParseCtx) ParseError!*ArithNode {
    var left = try parseCompMultiplicative(c);
    while (c.check(.add) or c.check(.sub)) {
        const is_add = c.check(.add);
        _ = c.advance();
        const right = try parseCompMultiplicative(c);
        left = if (is_add)
            try makeArithBin(c.alloc, .add, left, right)
        else
            try makeArithBin(c.alloc, .sub, left, right);
    }
    return left;
}

fn parseAtom(c: *ParseCtx) ParseError!*Node {
    if (c.check(.lparen)) {
        _ = c.advance();
        const inner = try parseEquivalence(c);
        try c.expect(.rparen);
        return inner;
    }

    const left = try parseCompExpr(c);

    if (isComparisonOp(c.cur().kind)) {
        const op = cmpOpFor(c.advance().kind);
        const right = try parseCompExpr(c);
        c.saw_comparison = true;
        return makeCmp(c.alloc, op, left, right);
    }

    if (asBareRef(left)) |name| {
        if (std.mem.indexOfScalar(u8, name, '.') != null) c.saw_dot = true;
        return makeLit(c.alloc, name);
    }

    // A bare arithmetic atom with no comparison at all (e.g. `sum(Power)`
    // alone as a "constraint") isn't Boolean-encodable either.
    c.saw_comparison = true;
    return makeInvalid(c.alloc);
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
    /// CNF-usable tree: null whenever the constraint should be dropped
    /// from the CNF -- either it touches an attribute reference (a dotted
    /// literal) or a numeric comparison.
    node: ?*Node,
    /// The complete tree regardless of `node`/`skip` -- includes `.cmp`
    /// and arithmetic sub-trees a CNF-only consumer can't use. Always
    /// non-null; used by the SMT writer/reader (parser/src/smt/writer.zig,
    /// parser/src/smt/reader.zig), which have no such restriction.
    full: *Node,
    saw_dot: bool,
    saw_comparison: bool,
    saw_bool_op: bool,
    end_pos: usize,
};

/// Parses one constraint expression starting at `tokens[start]`, stopping
/// as soon as the grammar cascade bottoms out (a NEWLINE token never
/// matches any continuation, so it's fine to hand this the rest of the
/// token stream rather than a pre-sliced line).
pub fn parseConstraint(alloc: Allocator, tokens: []const Token, start: usize) ParseError!ConstraintParse {
    var c = ParseCtx{ .alloc = alloc, .tokens = tokens, .pos = start };
    const node = try parseEquivalence(&c);
    const skip = c.saw_dot or c.saw_comparison;
    return .{
        .node = if (skip) null else node,
        .full = node,
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
        .cmp, .invalid => return ClauseError.UnknownFeature,
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
// This is the only construction path: pruning is a strict improvement
// (it can only produce the same clause set or a smaller
// logically-equivalent one, never a larger one), so there's no case
// where skipping it would be preferable.

pub const CnfError = ClauseError;

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

fn litHash(l: i32) u64 {
    const x: i64 = l;
    const u: u64 = @bitCast(x);
    return u *% 2654435761;
}

fn sigBit(l: i32) u6 {
    return @truncate(litHash(l) & 63);
}

fn computeSig(clause: []const i32) u64 {
    var s: u64 = 0;
    for (clause) |l| s |= (@as(u64, 1) << sigBit(l));
    return s;
}

/// `subsumes` with a bloom-filter pre-check: a signature mismatch proves
/// non-subset without touching either clause's literals.
fn subsumesSig(small_sig: u64, small: []const i32, big_sig: u64, big: []const i32) bool {
    if (small.len > big.len) return false;
    if (small_sig & big_sig != small_sig) return false;
    return subsumes(small, big);
}

const OccList = std.ArrayList(usize);
const OccMap = std.AutoHashMap(i32, OccList);

fn occAdd(alloc: Allocator, occ: *OccMap, lit: i32, id: usize) !void {
    const gop = try occ.getOrPut(lit);
    if (!gop.found_existing) gop.value_ptr.* = OccList.empty;
    try gop.value_ptr.append(alloc, id);
}

fn occLen(occ: *OccMap, lit: i32) usize {
    if (occ.getPtr(lit)) |list| return list.items.len;
    return 0;
}

/// Subsumption-pruned clause accumulator used while distributing one
/// constraint's own `.and_`/`.or_` NNF node -- bounds the intermediate
/// clause count during NNF-to-CNF distribution (a plain hash-based
/// exact-duplicate check would not suffice here: what actually needs
/// pruning is a longer clause dominated by a shorter, non-identical one
/// already present, which is the common case when distributing an OR over
/// an AND -- see README.md#cnf-clause-set-simplification).
///
/// Below `index_threshold` live entries, `insert` does the same O(kept)
/// linear scan `addWithSubsumption` always did (cheap in the common case:
/// most constraints produce only a handful of clauses, and building a
/// hash-based index has real constant-factor overhead that isn't worth
/// paying for a handful of comparisons). At and above the threshold, it
/// switches to an occurrence-indexed scan (`occ: literal -> entry
/// indices`), so a candidate is only ever compared against entries that
/// actually share a literal with it, not the whole list -- this is what
/// large per-constraint distributions (observed dominating total runtime
/// on linux-2.6.33.3.uvl: ~2.1s of ~2.3s total) need to stay fast. Both
/// modes produce identical output (the same subset relation, always
/// checked the same way via `subsumesSig`/`subsumes`) -- the threshold
/// only affects speed, never which clauses survive.
const IndexedKept = struct {
    items: std.ArrayList(?[]i32) = .empty,
    sigs: std.ArrayList(u64) = .empty,
    live_count: usize = 0,
    occ: ?OccMap = null,

    const index_threshold = 32;

    /// Builds the occurrence index from the current (guaranteed
    /// null-free, since linear mode always compacts via `swapRemove`
    /// rather than tombstoning) contents of `self.items`, backfilling
    /// `self.sigs` at the same time -- signatures aren't computed at all
    /// during linear mode, since plain `subsumes` never needs them.
    fn ensureIndex(self: *IndexedKept, alloc: Allocator) !void {
        if (self.occ != null) return;
        self.sigs = std.ArrayList(u64).empty;
        for (self.items.items) |maybe_c| {
            try self.sigs.append(alloc, computeSig(maybe_c.?));
        }
        var occ = OccMap.init(alloc);
        for (self.items.items, 0..) |maybe_c, idx| {
            for (maybe_c.?) |l| try occAdd(alloc, &occ, l, idx);
        }
        self.occ = occ;
    }

    fn insert(self: *IndexedKept, alloc: Allocator, candidate: []i32) !void {
        if (self.occ == null and self.live_count < index_threshold) {
            // Below index_threshold: plain O(kept) linear scan per
            // insertion. Compaction is via `swapRemove`, not tombstoning
            // -- the scanned array never grows beyond the current live
            // count. Tombstoning here would make this O(all insertions
            // ever attempted) for a node that does a lot of evicting
            // (observed: a ~2s run on linux-2.6.33.3.uvl became 3+
            // minutes).
            for (self.items.items) |maybe_k| {
                if (subsumes(maybe_k.?, candidate)) return; // candidate adds nothing new
            }
            var idx: usize = 0;
            while (idx < self.items.items.len) {
                if (subsumes(candidate, self.items.items[idx].?)) {
                    _ = self.items.swapRemove(idx);
                    self.live_count -= 1;
                } else {
                    idx += 1;
                }
            }
            try self.items.append(alloc, candidate);
            self.live_count += 1;
            return;
        }

        const candidate_sig = computeSig(candidate);
        try self.ensureIndex(alloc);
        const occ = &self.occ.?;

        // "Is candidate subsumed by an existing entry D" (D subset
        // candidate)? D need not contain candidate's cheapest-to-scan
        // literal -- it only needs its OWN literals to all be in
        // candidate -- so every literal of candidate must be checked
        // (unlike subsumption.zig's global batch pass, an already-settled
        // entry here never gets a "later turn" to discover it subsumes a
        // new arrival from its own side, so this direction can't be
        // narrowed to a single pivot the way that pass's queue-driven
        // eventual-reprocessing argument allows).
        // No snapshot needed: this loop never mutates `occ`/`items`, only
        // reads and possibly returns early.
        for (candidate) |l| {
            const list = occ.getPtr(l) orelse continue;
            for (list.items) |idx| {
                const k = self.items.items[idx] orelse continue;
                if (subsumesSig(self.sigs.items[idx], k, candidate_sig, candidate)) return; // candidate adds nothing new
            }
        }

        // "Does candidate subsume an existing entry D" (candidate subset
        // D)? Any such D must contain EVERY literal of candidate, so it
        // appears in occ[l] for every l in candidate -- scanning just the
        // cheapest one is sufficient here.
        var pivot = candidate[0];
        var pivot_len = occLen(occ, pivot);
        for (candidate[1..]) |l| {
            const len = occLen(occ, l);
            if (len < pivot_len) {
                pivot = l;
                pivot_len = len;
            }
        }
        // No snapshot needed here either: this loop only nulls out entries
        // in `self.items`, never appends/removes from `occ[pivot]`'s own
        // list (that only happens once, below, for candidate's own
        // literals, after this loop has finished).
        if (occ.getPtr(pivot)) |list| {
            for (list.items) |idx| {
                const k = self.items.items[idx] orelse continue;
                if (subsumesSig(candidate_sig, candidate, self.sigs.items[idx], k)) {
                    self.items.items[idx] = null;
                    self.live_count -= 1;
                }
            }
        }

        const new_idx = self.items.items.len;
        try self.items.append(alloc, candidate);
        try self.sigs.append(alloc, candidate_sig);
        self.live_count += 1;
        for (candidate) |l| try occAdd(alloc, occ, l, new_idx);
    }

    fn toOwnedSlice(self: *IndexedKept, alloc: Allocator) ![][]i32 {
        var out = std.ArrayList([]i32).empty;
        for (self.items.items) |maybe_c| {
            if (maybe_c) |c| try out.append(alloc, c);
        }
        return out.toOwnedSlice(alloc);
    }
};

fn buildCnf(alloc: Allocator, features2ids: *const std.StringHashMap(i32), n: *Node) CnfError![][]i32 {
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
            const a = try buildCnf(alloc, features2ids, ab[0]);
            const b = try buildCnf(alloc, features2ids, ab[1]);
            var kept = IndexedKept{};
            for (a) |c| try kept.insert(alloc, c);
            for (b) |c| try kept.insert(alloc, c);
            return kept.toOwnedSlice(alloc);
        },
        .or_ => |ab| {
            const a = try buildCnf(alloc, features2ids, ab[0]);
            const b = try buildCnf(alloc, features2ids, ab[1]);
            var kept = IndexedKept{};
            for (a) |ca| {
                for (b) |cb| {
                    const u = (try unionClause(alloc, ca, cb)) orelse continue;
                    try kept.insert(alloc, u);
                }
            }
            return kept.toOwnedSlice(alloc);
        },
        .cmp, .invalid => return ClauseError.UnknownFeature,
        .implies, .equiv => unreachable, // n is already NNF'd
    }
}

/// Converts one constraint to CNF: negation normal form, then
/// distribution of `or` over `and`, then literal resolution -- see the
/// module doc comment above for why the distribute step itself is
/// subsumption-pruned rather than a plain, unguarded pairwise distribute.
pub fn generateClauses(alloc: Allocator, features2ids: *const std.StringHashMap(i32), root: *Node) CnfError![][]i32 {
    const in_nnf = try nnf(alloc, root, false);
    return buildCnf(alloc, features2ids, in_nnf);
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
    // `.full` is still built even though `.node` is nulled.
    try std.testing.expect(parsed.full.* == .cmp);
    try std.testing.expectEqual(CmpOp.gt, parsed.full.cmp.op);
    try std.testing.expect(parsed.full.cmp.lhs.* == .ref);
    try std.testing.expectEqualStrings("A", parsed.full.cmp.lhs.ref);
    try std.testing.expect(parsed.full.cmp.rhs.* == .num);
    try std.testing.expectEqualStrings("3", parsed.full.cmp.rhs.num);
}

const lexer = @import("lexer");

fn parseText(alloc: Allocator, text: []const u8) !ConstraintParse {
    const toks = try lexer.tokenize(alloc, text);
    return parseConstraint(alloc, toks, 0);
}

test "arithmetic ops build a nested left-associative tree" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // A + B * 2 > 3  ==  A + (B * 2) > 3 (mul binds tighter than add)
    const parsed = try parseText(alloc, "A + B * 2 > 3");
    try std.testing.expect(parsed.node == null);
    try std.testing.expect(parsed.full.* == .cmp);
    const lhs = parsed.full.cmp.lhs;
    try std.testing.expect(lhs.* == .add);
    try std.testing.expect(lhs.add[0].* == .ref);
    try std.testing.expectEqualStrings("A", lhs.add[0].ref);
    try std.testing.expect(lhs.add[1].* == .mul);
    try std.testing.expectEqualStrings("B", lhs.add[1].mul[0].ref);
    try std.testing.expectEqualStrings("2", lhs.add[1].mul[1].num);
}

test "2-arg aggregate call captures scope and attribute separately" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseText(alloc, "sum(SomeFeature, Power) > 120");
    try std.testing.expect(parsed.full.* == .cmp);
    const lhs = parsed.full.cmp.lhs;
    try std.testing.expect(lhs.* == .aggregate);
    try std.testing.expectEqual(AggFunc.sum, lhs.aggregate.func);
    try std.testing.expectEqualStrings("SomeFeature", lhs.aggregate.scope.?);
    try std.testing.expectEqualStrings("Power", lhs.aggregate.arg);
}

test "1-arg aggregate call has no scope" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseText(alloc, "avg(Power) > 3");
    const lhs = parsed.full.cmp.lhs;
    try std.testing.expect(lhs.* == .aggregate);
    try std.testing.expectEqual(AggFunc.avg, lhs.aggregate.func);
    try std.testing.expect(lhs.aggregate.scope == null);
    try std.testing.expectEqualStrings("Power", lhs.aggregate.arg);
}

test "floor and ceil aggregates parse" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const floor_parsed = try parseText(alloc, "floor(Price) > 3");
    try std.testing.expectEqual(AggFunc.floor, floor_parsed.full.cmp.lhs.aggregate.func);

    const ceil_parsed = try parseText(alloc, "ceil(Price) > 3");
    try std.testing.expectEqual(AggFunc.ceil, ceil_parsed.full.cmp.lhs.aggregate.func);
}

test "len aggregate and string literal comparison" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseText(alloc, "len(Name) == 3");
    try std.testing.expectEqual(CmpOp.eq, parsed.full.cmp.op);
    try std.testing.expectEqual(AggFunc.len, parsed.full.cmp.lhs.aggregate.func);

    const str_parsed = try parseText(alloc, "Name == 'Fun'");
    try std.testing.expect(str_parsed.full.cmp.rhs.* == .str);
    try std.testing.expectEqualStrings("'Fun'", str_parsed.full.cmp.rhs.str);
}

test "a bare arithmetic atom with no comparison is still not boolean-encodable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseText(alloc, "sum(Power)");
    try std.testing.expect(parsed.node == null);
    try std.testing.expect(parsed.saw_comparison);
    // The arithmetic sub-tree itself isn't retained outside a comparison
    // (there's nothing to compare it to), so `.full` degrades to
    // `.invalid` here, same as `.node` -- this shape is not a valid
    // constraint under any interpretation, boolean or otherwise.
    try std.testing.expect(parsed.full.* == .invalid);
}

test "a plain boolean constraint still produces a matching .full and .node" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const parsed = try parseText(alloc, "A => B");
    try std.testing.expect(parsed.node != null);
    try std.testing.expect(parsed.node.? == parsed.full);
    try std.testing.expect(parsed.full.* == .implies);
}

test "IndexedKept: subsumption still correct once past the linear-scan threshold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var kept = IndexedKept{};
    // Push well past index_threshold (32) with distinct unit clauses so
    // every insertion after the threshold goes through the indexed path.
    var i: i32 = 1;
    while (i <= 50) : (i += 1) {
        const c = try alloc.alloc(i32, 1);
        c[0] = i;
        try kept.insert(alloc, c);
    }
    try std.testing.expectEqual(@as(usize, 50), kept.live_count);

    // A clause subsumed by an existing unit clause (here [1]) must still
    // be rejected via the indexed path.
    const redundant = try alloc.alloc(i32, 2);
    redundant[0] = 1;
    redundant[1] = 99;
    try kept.insert(alloc, redundant);
    try std.testing.expectEqual(@as(usize, 50), kept.live_count);

    // A new unit clause on a fresh variable must evict any existing
    // clause it subsumes (here, none exist yet for var 100, so it's a
    // pure addition) and still be findable afterwards.
    const fresh = try alloc.alloc(i32, 1);
    fresh[0] = 100;
    try kept.insert(alloc, fresh);
    try std.testing.expectEqual(@as(usize, 51), kept.live_count);

    const out = try kept.toOwnedSlice(alloc);
    try std.testing.expectEqual(@as(usize, 51), out.len);
    var found_redundant = false;
    for (out) |c| {
        if (c.len == 2 and c[0] == 1 and c[1] == 99) found_redundant = true;
    }
    try std.testing.expect(!found_redundant);
}

test "IndexedKept: a later clause evicts an earlier one it subsumes, past threshold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var kept = IndexedKept{};
    // Fill with unrelated clauses to cross the threshold first.
    var i: i32 = 1;
    while (i <= 40) : (i += 1) {
        const c = try alloc.alloc(i32, 2);
        c[0] = i;
        c[1] = i + 1000;
        try kept.insert(alloc, c);
    }
    // Now insert a longer clause on a fresh variable pair...
    const long_clause = try alloc.alloc(i32, 3);
    long_clause[0] = 5000;
    long_clause[1] = 5001;
    long_clause[2] = 5002;
    try kept.insert(alloc, long_clause);
    try std.testing.expectEqual(@as(usize, 41), kept.live_count);

    // ...then a unit clause that subsumes it -- must evict the longer one
    // even though both were inserted after crossing the index threshold.
    const unit = try alloc.alloc(i32, 1);
    unit[0] = 5001;
    try kept.insert(alloc, unit);
    try std.testing.expectEqual(@as(usize, 41), kept.live_count); // long_clause evicted, unit added

    const out = try kept.toOwnedSlice(alloc);
    var found_long = false;
    for (out) |c| {
        if (c.len == 3) found_long = true;
    }
    try std.testing.expect(!found_long);
}



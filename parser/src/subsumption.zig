const std = @import("std");
const Allocator = std.mem.Allocator;

/// Canonical clause literal order for this whole pipeline's output:
/// ascending by absolute value (e.g. `[1, -2, 3, -4]`), so a clause and
/// its negated counterpart on the same variable sort adjacently and every
/// clause has one unambiguous textual form regardless of which pass
/// produced it. `simplify` below normalizes every input clause to this
/// order (see the dedupe/sort step at the top of the loop over `input`).
fn absLess(_: void, a: i32, b: i32) bool {
    return @abs(a) < @abs(b);
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

fn contains(clause: []const i32, lit: i32) bool {
    for (clause) |x| {
        if (x == lit) return true;
    }
    return false;
}

/// True iff `small` (sorted ascending by |lit|) is a subset of `big` (same
/// order). Signature check is a necessary-not-sufficient pre-filter, per
/// spec: a mismatch proves non-subset without touching either clause's
/// literals; a match still requires the real merge-walk below.
fn isSubset(small_sig: u64, small: []const i32, big_sig: u64, big: []const i32) bool {
    if (small.len > big.len) return false;
    if (small_sig & big_sig != small_sig) return false;
    var i: usize = 0;
    var j: usize = 0;
    while (i < small.len and j < big.len) {
        if (small[i] == big[j]) {
            i += 1;
            j += 1;
        } else if (absLess({}, small[i], big[j])) {
            return false;
        } else {
            j += 1;
        }
    }
    return i == small.len;
}

/// Returns Some(l) if `d` can be shortened by removing literal `l`
/// (`l` ∈ d, `-l` ∈ c), i.e. `(c \ {-l}) ⊆ (d \ {l})`. Returns null if no
/// single clashing literal exists (either plain subsumption -- handled
/// separately -- or no strengthening relation at all).
fn tryStrengthen(c: []const i32, d: []const i32) ?i32 {
    if (c.len > d.len + 1) return null;
    var found_flip: ?i32 = null;
    for (c) |lit| {
        if (contains(d, lit)) continue;
        if (contains(d, -lit)) {
            if (found_flip != null) return null;
            found_flip = -lit;
        } else {
            return null;
        }
    }
    return found_flip;
}

const OccList = std.ArrayList(usize);
const OccMap = std.AutoHashMap(i32, OccList);

fn occAdd(alloc: Allocator, occ: *OccMap, lit: i32, id: usize) !void {
    const gop = try occ.getOrPut(lit);
    if (!gop.found_existing) gop.value_ptr.* = OccList.empty;
    try gop.value_ptr.append(alloc, id);
}

fn occRemove(occ: *OccMap, lit: i32, id: usize) void {
    if (occ.getPtr(lit)) |list| {
        for (list.items, 0..) |x, idx| {
            if (x == id) {
                _ = list.swapRemove(idx);
                return;
            }
        }
    }
}

fn occLen(occ: *OccMap, lit: i32) usize {
    if (occ.getPtr(lit)) |list| return list.items.len;
    return 0;
}

fn requeueNeighbors(
    alloc: Allocator,
    occ: *OccMap,
    clauses: *std.ArrayList(?[]i32),
    in_queue: *std.DynamicBitSet,
    queue: *Queue,
    lits: []const i32,
) !void {
    for (lits) |l| {
        if (occ.getPtr(l)) |list| {
            for (list.items) |other_id| {
                if (clauses.items[other_id] == null) continue;
                if (in_queue.isSet(other_id)) continue;
                try queue.pushBack(alloc, other_id);
                in_queue.set(other_id);
            }
        }
    }
}

/// FIFO over clause IDs, backed by a growable array with a head cursor.
/// Amortized O(1) push/pop; periodically compacts the consumed prefix so
/// memory doesn't grow unbounded over a long run with heavy requeueing.
const Queue = struct {
    items: std.ArrayList(usize) = .empty,
    head: usize = 0,

    fn pushBack(self: *Queue, alloc: Allocator, id: usize) !void {
        try self.items.append(alloc, id);
    }

    fn popFront(self: *Queue) ?usize {
        if (self.head >= self.items.items.len) return null;
        const id = self.items.items[self.head];
        self.head += 1;
        if (self.head > 1024 and self.head * 2 > self.items.items.len) {
            const remaining = self.items.items.len - self.head;
            std.mem.copyForwards(usize, self.items.items[0..remaining], self.items.items[self.head..]);
            self.items.shrinkRetainingCapacity(remaining);
            self.head = 0;
        }
        return id;
    }
};

pub const SimplifyResult = struct {
    clauses: [][]i32,
    /// Parallel to `clauses`: for each surviving output clause, the index
    /// into the original `input` slice it came from (or, if `tags_in` was
    /// passed to `simplify`, that tag's value for the surviving clause's
    /// input index). Lets a caller that tagged each input clause with e.g.
    /// "which source constraint produced this clause" find out which
    /// clauses (and therefore which tags) survived simplification, without
    /// having to reconstruct that from clause content (unreliable: content
    /// is preserved verbatim only when `enable_ssr` is false).
    tags: []usize,
    removed_by_subsumption: usize,
    literals_removed_by_ssr: usize,
    tautologies_removed: usize,
    unsat: bool,
};

/// A genuinely empty clause LIST is vacuously satisfiable (no constraints
/// at all) -- the opposite of what UNSAT means. DIMACS represents UNSAT
/// via one literal empty CLAUSE (a clause with zero literals, which can
/// never be satisfied); `cnf.writeDimacs` already handles a zero-length
/// clause correctly (writes a bare "0" line), so this is all downstream
/// consumers need to see the formula as UNSAT rather than trivially SAT.
fn unsatResult(alloc: Allocator, removed: usize, ssr: usize, taut: usize) !SimplifyResult {
    const out = try alloc.alloc([]i32, 1);
    out[0] = try alloc.alloc(i32, 0);
    return .{
        .clauses = out,
        // No single input clause "is" the empty clause; there's nothing
        // meaningful to tag it with.
        .tags = try alloc.alloc(usize, 0),
        .removed_by_subsumption = removed,
        .literals_removed_by_ssr = ssr,
        .tautologies_removed = taut,
        .unsat = true,
    };
}

/// Global clause-set simplification via subsumption elimination and
/// self-subsuming resolution (strengthening), run to a fixpoint.
///
/// Candidate generation deliberately differs from the most literal reading
/// of "pivot = one literal, candidates = occ[pivot] used for everything":
/// subsumption candidates come from occ[l] (same-sign occurrence lists,
/// since C ⊆ D requires D to contain every literal of C with the same
/// sign -- picking the cheapest such l as pivot is sufficient, because any
/// actual subsumption relationship is still found when the *other* clause
/// of the pair is processed, using its own pivot). Strengthening
/// candidates, however, come from occ[-l] for *every* literal l in the
/// popped clause: self-subsuming resolution is inherently about a
/// complementary literal, so a same-sign-only occurrence index can never
/// find it. This matters concretely for the unit-clause UNSAT case
/// ({1} vs {-1}): the two clauses share no literal value at all (one has
/// +1, the other -1), so a pure same-sign pivot scan from *either* side
/// never puts them in the same candidate list, no matter the processing
/// order -- only the complementary-literal scan does. This is standard in
/// real SAT preprocessors (e.g. SatELite/MiniSat's self-subsuming
/// resolution): same-sign occurrence lists for subsumption, complementary
/// for resolution-based strengthening.
///
/// `enable_ssr` gates self-subsuming resolution (strengthening). Both
/// subsumption elimination and SSR preserve exact logical equivalence
/// (the same set of satisfying assignments over the same variables, not
/// merely equisatisfiability -- SSR introduces no new variables and is a
/// standard, provably-exact transformation), so this flag is not a
/// soundness knob. It exists because SSR actively rewrites surviving
/// clauses' literal content, which a downstream consumer that depends on
/// clauses keeping a specific *syntactic* shape (e.g. `recovery.zig`'s
/// hierarchy reconstruction, which expects to find plain 2-literal
/// `{-child, parent}` edges) can't tolerate even though the formula
/// remains exactly equivalent. Pass `false` on any path whose output
/// feeds such a consumer; `true` is safe (and more effective) anywhere
/// only the CNF's satisfying assignments matter.
pub fn simplify(alloc: Allocator, input: []const []const i32, enable_ssr: bool) !SimplifyResult {
    return simplifyTagged(alloc, input, null, enable_ssr);
}

/// Same as `simplify`, but also tracks provenance: `tags_in`, if non-null,
/// must be the same length as `input` and gives each input clause an
/// arbitrary caller-defined tag (e.g. "which source constraint this clause
/// came from"); `null` defaults each clause's tag to its own index in
/// `input`. `SimplifyResult.tags` then gives, for each surviving output
/// clause, the tag of the input clause it came from.
pub fn simplifyTagged(alloc: Allocator, input: []const []const i32, tags_in: ?[]const usize, enable_ssr: bool) !SimplifyResult {
    var clauses = std.ArrayList(?[]i32).empty;
    var sigs = std.ArrayList(u64).empty;
    var tags = std.ArrayList(usize).empty;
    var occ = OccMap.init(alloc);
    var tautologies_removed: usize = 0;

    for (input, 0..) |raw, in_idx| {
        try tags.append(alloc, if (tags_in) |t| t[in_idx] else in_idx);
        var c = try alloc.dupe(i32, raw);
        std.mem.sort(i32, c, {}, absLess);
        // dedupe (a clause is a set, not a multiset)
        var w: usize = 0;
        for (c) |l| {
            if (w == 0 or c[w - 1] != l) {
                c[w] = l;
                w += 1;
            }
        }
        c = c[0..w];

        var taut = false;
        for (c, 0..) |l, idx| {
            if (idx + 1 < c.len and c[idx + 1] == -l) {
                taut = true;
                break;
            }
        }
        if (taut) {
            tautologies_removed += 1;
            try clauses.append(alloc, null);
            try sigs.append(alloc, 0);
            continue;
        }

        const id = clauses.items.len;
        try clauses.append(alloc, c);
        try sigs.append(alloc, computeSig(c));
        for (c) |l| try occAdd(alloc, &occ, l, id);
    }

    const n = clauses.items.len;
    var in_queue = try std.DynamicBitSet.initEmpty(alloc, n);
    var queue = Queue{};

    {
        var order = try alloc.alloc(usize, n);
        var order_len: usize = 0;
        for (0..n) |id| {
            if (clauses.items[id] != null) {
                order[order_len] = id;
                order_len += 1;
            }
        }
        order = order[0..order_len];
        const Ctx = struct {
            clauses: *std.ArrayList(?[]i32),
            pub fn lessThan(self: @This(), a: usize, b: usize) bool {
                return self.clauses.items[a].?.len < self.clauses.items[b].?.len;
            }
        };
        std.mem.sort(usize, order, Ctx{ .clauses = &clauses }, Ctx.lessThan);
        for (order) |id| {
            try queue.pushBack(alloc, id);
            in_queue.set(id);
        }
    }

    var removed_by_subsumption: usize = 0;
    var literals_removed_by_ssr: usize = 0;

    while (queue.popFront()) |c_id| {
        in_queue.unset(c_id);
        if (clauses.items[c_id] == null) continue;

        // --- subsumption candidates: cheapest same-sign occurrence list ---
        {
            const c = clauses.items[c_id].?;
            var pivot = c[0];
            var pivot_len = occLen(&occ, pivot);
            for (c[1..]) |l| {
                const len = occLen(&occ, l);
                if (len < pivot_len) {
                    pivot = l;
                    pivot_len = len;
                }
            }

            const candidates = if (occ.getPtr(pivot)) |list| try alloc.dupe(usize, list.items) else &[_]usize{};
            for (candidates) |d_id| {
                if (d_id == c_id or clauses.items[d_id] == null) continue;
                const c_now = clauses.items[c_id] orelse break; // c_id may have been deleted below
                const d = clauses.items[d_id].?;

                if (c_now.len <= d.len and isSubset(sigs.items[c_id], c_now, sigs.items[d_id], d)) {
                    try requeueNeighbors(alloc, &occ, &clauses, &in_queue, &queue, d);
                    for (d) |l| occRemove(&occ, l, d_id);
                    clauses.items[d_id] = null;
                    removed_by_subsumption += 1;
                    continue;
                }
                if (d.len <= c_now.len and isSubset(sigs.items[d_id], d, sigs.items[c_id], c_now)) {
                    try requeueNeighbors(alloc, &occ, &clauses, &in_queue, &queue, c_now);
                    for (c_now) |l| occRemove(&occ, l, c_id);
                    clauses.items[c_id] = null;
                    removed_by_subsumption += 1;
                    break;
                }
            }
        }

        if (clauses.items[c_id] == null) continue;
        if (!enable_ssr) continue;

        // --- strengthening candidates: complementary occurrence lists ---
        var c_now = clauses.items[c_id].?;
        var lit_idx: usize = 0;
        while (lit_idx < c_now.len) : (lit_idx += 1) {
            const l = c_now[lit_idx];
            const complist = if (occ.getPtr(-l)) |list| try alloc.dupe(usize, list.items) else &[_]usize{};
            for (complist) |d_id| {
                if (d_id == c_id or clauses.items[d_id] == null) continue;
                c_now = clauses.items[c_id] orelse break; // strengthening below may shrink/delete c
                var d = clauses.items[d_id].?;

                if (tryStrengthen(c_now, d)) |flip| {
                    occRemove(&occ, flip, d_id);
                    const new_d = try alloc.alloc(i32, d.len - 1);
                    var k: usize = 0;
                    for (d) |x| {
                        if (x != flip) {
                            new_d[k] = x;
                            k += 1;
                        }
                    }
                    try requeueNeighbors(alloc, &occ, &clauses, &in_queue, &queue, d);
                    clauses.items[d_id] = new_d;
                    sigs.items[d_id] = computeSig(new_d);
                    literals_removed_by_ssr += 1;
                    if (new_d.len == 0) {
                        return unsatResult(alloc, removed_by_subsumption, literals_removed_by_ssr, tautologies_removed);
                    }
                    continue;
                }
                d = clauses.items[d_id].?; // re-fetch: unchanged if we get here
                if (tryStrengthen(d, c_now)) |flip2| {
                    occRemove(&occ, flip2, c_id);
                    const new_c = try alloc.alloc(i32, c_now.len - 1);
                    var k: usize = 0;
                    for (c_now) |x| {
                        if (x != flip2) {
                            new_c[k] = x;
                            k += 1;
                        }
                    }
                    try requeueNeighbors(alloc, &occ, &clauses, &in_queue, &queue, c_now);
                    clauses.items[c_id] = new_c;
                    sigs.items[c_id] = computeSig(new_c);
                    literals_removed_by_ssr += 1;
                    if (new_c.len == 0) {
                        return unsatResult(alloc, removed_by_subsumption, literals_removed_by_ssr, tautologies_removed);
                    }
                    c_now = new_c;
                    lit_idx = 0; // c changed shape/length; restart the literal scan for it
                    continue;
                }
            }
        }
    }

    var out = std.ArrayList([]i32).empty;
    var out_tags = std.ArrayList(usize).empty;
    for (clauses.items, 0..) |maybe_c, id| {
        if (maybe_c) |c| {
            try out.append(alloc, c);
            try out_tags.append(alloc, tags.items[id]);
        }
    }

    return .{
        .clauses = try out.toOwnedSlice(alloc),
        .tags = try out_tags.toOwnedSlice(alloc),
        .removed_by_subsumption = removed_by_subsumption,
        .literals_removed_by_ssr = literals_removed_by_ssr,
        .tautologies_removed = tautologies_removed,
        .unsat = false,
    };
}

fn clauseSet(alloc: Allocator, clauses: [][]i32) !std.AutoHashMap(u64, void) {
    var set = std.AutoHashMap(u64, void).init(alloc);
    for (clauses) |c| {
        var h = std.hash.Wyhash.init(0);
        h.update(std.mem.sliceAsBytes(c));
        try set.put(h.final(), {});
    }
    return set;
}

fn expectClauseSetEqual(alloc: Allocator, expected: []const []const i32, actual: [][]i32) !void {
    try std.testing.expectEqual(expected.len, actual.len);
    var exp_norm = std.ArrayList([]i32).empty;
    for (expected) |e| {
        const copy = try alloc.dupe(i32, e);
        std.mem.sort(i32, copy, {}, absLess);
        try exp_norm.append(alloc, copy);
    }
    var expected_set = try clauseSet(alloc, exp_norm.items);
    var actual_set = try clauseSet(alloc, actual);
    try std.testing.expectEqual(expected_set.count(), actual_set.count());
    var it = expected_set.keyIterator();
    while (it.next()) |k| {
        try std.testing.expect(actual_set.contains(k.*));
    }
}

test "1: basic subsumption" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ 1, 2, 3 } };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{&.{ 1, 2 }}, result.clauses);
    try std.testing.expectEqual(@as(usize, 1), result.removed_by_subsumption);
}

test "2: self-subsumption / strengthening" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ -1, 2, 3 } };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{ &.{ 1, 2 }, &.{ 2, 3 } }, result.clauses);
    try std.testing.expectEqual(@as(usize, 1), result.literals_removed_by_ssr);
}

test "3: tautology removal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, -1, 2 }, &.{ 1, 2 } };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{&.{ 1, 2 }}, result.clauses);
    try std.testing.expectEqual(@as(usize, 1), result.tautologies_removed);
}

test "4: duplicate clause -> keep one" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ 1, 2 } };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{&.{ 1, 2 }}, result.clauses);
}

test "5: empty clause / UNSAT detection" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{1}, &.{-1} };
    const result = try simplify(alloc, &input, true);
    try std.testing.expect(result.unsat);
    // must contain the empty clause, not an empty clause LIST -- a clause
    // list with zero clauses is vacuously satisfiable, the opposite of
    // what UNSAT means in DIMACS.
    try std.testing.expectEqual(@as(usize, 1), result.clauses.len);
    try std.testing.expectEqual(@as(usize, 0), result.clauses[0].len);
}

test "6: no spurious changes on already-minimal input" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ 3, 4 }, &.{5} };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{ &.{ 1, 2 }, &.{ 3, 4 }, &.{5} }, result.clauses);
    try std.testing.expectEqual(@as(usize, 0), result.removed_by_subsumption);
    try std.testing.expectEqual(@as(usize, 0), result.literals_removed_by_ssr);
}

test "7: chained strengthening reaches fixpoint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    // (1∨2∨3) ∧ (¬1∨2∨3) ∧ (¬2∨3) is logically equivalent to (3) alone:
    // if 3 is false, clause 3 forces ¬2, then clause 1 forces 1, then
    // clause 2 forces ¬1 -- contradiction, so 3 must be true.
    const input = [_][]const i32{ &.{ 1, 2, 3 }, &.{ -1, 2, 3 }, &.{ -2, 3 } };
    const result = try simplify(alloc, &input, true);
    try expectClauseSetEqual(alloc, &[_][]const i32{&.{3}}, result.clauses);
}

test "enable_ssr=false: subsumption and dedup still work" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ 1, 2, 3 }, &.{ 1, 2 } };
    const result = try simplify(alloc, &input, false);
    try expectClauseSetEqual(alloc, &[_][]const i32{&.{ 1, 2 }}, result.clauses);
    try std.testing.expectEqual(@as(usize, 0), result.literals_removed_by_ssr);
}

test "enable_ssr=false: strengthening opportunity is left alone" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    // Same input as test 2 -- with SSR disabled, neither clause changes:
    // {1,2} and {-1,2,3} share no subset relation and SSR is the only
    // rule that would touch them.
    const input = [_][]const i32{ &.{ 1, 2 }, &.{ -1, 2, 3 } };
    const result = try simplify(alloc, &input, false);
    try expectClauseSetEqual(alloc, &[_][]const i32{ &.{ 1, 2 }, &.{ -1, 2, 3 } }, result.clauses);
    try std.testing.expectEqual(@as(usize, 0), result.literals_removed_by_ssr);
}

test "enable_ssr=false: unit-clause conflict is NOT detected as UNSAT" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    // {1} vs {-1} share no literal value at all, so only the
    // complementary-literal SSR scan can ever find this pair -- with SSR
    // off, plain subsumption has no way to detect the conflict.
    const input = [_][]const i32{ &.{1}, &.{-1} };
    const result = try simplify(alloc, &input, false);
    try std.testing.expect(!result.unsat);
    try std.testing.expectEqual(@as(usize, 2), result.clauses.len);
}

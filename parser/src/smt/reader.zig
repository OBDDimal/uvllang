//! A minimal SMT-LIB 2 reader scoped to exactly the dialect `smt.zig`'s
//! writer emits (`declare-const` of Bool/Int/Real/String,
//! `assert`/`and`/`or`/`not`/`=>`/`=`/`distinct`/`<`/`<=`/`>`/`>=`/
//! `+`/`-`/`*`/`/`, `check-sat`/`get-model`) -- not general SMT-LIB 2. It
//! backs `any2uvl`'s `.smt2` input support: a generic S-expression parser
//! (`SExpr`), then a semantic pass that either flattens a purely-Boolean
//! `assert` into the same `[]const i32` clause shape `recovery.zig`'s
//! `parseDimacs` produces (reusing `constraint.generateClauses`, the same
//! code UVL source constraints go through), or -- for anything involving
//! a non-Bool sort (`ite`, arithmetic, a typed feature's `_val` companion,
//! an attribute var) -- renders it back into UVL constraint syntax as a
//! residual, verbatim constraint text line, via `recovery.recoverFromParsed`'s
//! `extra_constraints` parameter.
//!
//! An assert that isn't representable in either form at all (e.g. it
//! contains `ite`/`to_int`/`str.len`, which have no UVL constraint-syntax
//! equivalent) is dropped with a warning rather than emitted as
//! syntactically invalid UVL -- this is the same "sum(...)/avg(...)
//! shorthand isn't reconstructed from its expanded ite form" fidelity gap
//! documented for the writer, just observed from the reader's side: never
//! producing broken output takes priority over full round-trip fidelity
//! for the small slice of content this can't represent.

const std = @import("std");
const Allocator = std.mem.Allocator;
const recovery = @import("recovery");
const constraint = @import("constraint");
const ParsedDimacs = recovery.ParsedDimacs;

pub const SExpr = union(enum) {
    atom: []const u8,
    list: []SExpr,
};

pub const ParseError = error{ UnexpectedEnd, UnexpectedChar } || Allocator.Error;

const SParser = struct {
    src: []const u8,
    pos: usize = 0,

    fn skipWs(p: *SParser) void {
        while (p.pos < p.src.len) {
            const c = p.src[p.pos];
            if (c == ' ' or c == '\t' or c == '\n' or c == '\r') {
                p.pos += 1;
                continue;
            }
            if (c == ';') {
                while (p.pos < p.src.len and p.src[p.pos] != '\n') p.pos += 1;
                continue;
            }
            break;
        }
    }

    fn parseExpr(p: *SParser, alloc: Allocator) ParseError!SExpr {
        p.skipWs();
        if (p.pos >= p.src.len) return ParseError.UnexpectedEnd;
        const c = p.src[p.pos];
        if (c == '(') {
            p.pos += 1;
            var items = std.ArrayList(SExpr).empty;
            while (true) {
                p.skipWs();
                if (p.pos >= p.src.len) return ParseError.UnexpectedEnd;
                if (p.src[p.pos] == ')') {
                    p.pos += 1;
                    break;
                }
                try items.append(alloc, try p.parseExpr(alloc));
            }
            return .{ .list = try items.toOwnedSlice(alloc) };
        }
        if (c == '"') {
            const start = p.pos;
            p.pos += 1;
            while (p.pos < p.src.len) {
                if (p.src[p.pos] == '"') {
                    if (p.pos + 1 < p.src.len and p.src[p.pos + 1] == '"') {
                        p.pos += 2;
                        continue;
                    }
                    p.pos += 1;
                    break;
                }
                p.pos += 1;
            }
            return .{ .atom = p.src[start..p.pos] };
        }
        if (c == '|') {
            const start = p.pos;
            p.pos += 1;
            while (p.pos < p.src.len and p.src[p.pos] != '|') p.pos += 1;
            if (p.pos < p.src.len) p.pos += 1;
            return .{ .atom = p.src[start..p.pos] };
        }
        const start = p.pos;
        while (p.pos < p.src.len) {
            const ch = p.src[p.pos];
            if (ch == ' ' or ch == '\t' or ch == '\n' or ch == '\r' or ch == '(' or ch == ')') break;
            p.pos += 1;
        }
        if (p.pos == start) return ParseError.UnexpectedChar;
        return .{ .atom = p.src[start..p.pos] };
    }
};

/// Parses every top-level form in `src` (typically `declare-const`,
/// `assert`, `check-sat`, `get-model`).
pub fn parseTop(alloc: Allocator, src: []const u8) ParseError![]SExpr {
    var p = SParser{ .src = src };
    var items = std.ArrayList(SExpr).empty;
    while (true) {
        p.skipWs();
        if (p.pos >= p.src.len) break;
        try items.append(alloc, try p.parseExpr(alloc));
    }
    return items.toOwnedSlice(alloc);
}

fn stripPipe(s: []const u8) []const u8 {
    if (s.len >= 2 and s[0] == '|' and s[s.len - 1] == '|') return s[1 .. s.len - 1];
    return s;
}

fn needsUvlQuoting(name: []const u8) bool {
    if (name.len == 0) return true;
    if (std.ascii.isDigit(name[0])) return true;
    for (name) |c| {
        if (!(std.ascii.isAlphanumeric(c) or c == '_' or c == '-')) return true;
    }
    return false;
}

/// Converts an SMT-LIB identifier (possibly `|...|`-quoted) back into a
/// UVL-safe feature/attribute name (possibly `"..."`-quoted). Not
/// guaranteed byte-identical to whatever the original UVL source used
/// (e.g. a single-quoted original becomes double-quoted here) -- the
/// semantic name is preserved, not necessarily the original quote style.
fn toUvlName(alloc: Allocator, smt_ident: []const u8) ![]const u8 {
    const raw = stripPipe(smt_ident);
    if (!needsUvlQuoting(raw)) return raw;
    return std.fmt.allocPrint(alloc, "\"{s}\"", .{raw});
}

/// Strips the `_val` suffix `smt.zig`'s writer appends to a typed
/// feature's companion const, restoring the bare feature reference.
fn stripValSuffix(name: []const u8) []const u8 {
    const suffix = "_val";
    if (std.mem.endsWith(u8, name, suffix)) return name[0 .. name.len - suffix.len];
    return name;
}

fn isPureBoolean(e: SExpr, bool_names: *const std.StringHashMap(void)) bool {
    switch (e) {
        .atom => |a| {
            if (std.mem.eql(u8, a, "true") or std.mem.eql(u8, a, "false")) return true;
            return bool_names.contains(a);
        },
        .list => |items| {
            if (items.len == 0) return false;
            if (items[0] != .atom) return false;
            const head = items[0].atom;
            if (std.mem.eql(u8, head, "not") and items.len == 2) {
                return isPureBoolean(items[1], bool_names);
            }
            if ((std.mem.eql(u8, head, "and") or std.mem.eql(u8, head, "or") or
                std.mem.eql(u8, head, "=>") or std.mem.eql(u8, head, "=")) and items.len == 3)
            {
                return isPureBoolean(items[1], bool_names) and isPureBoolean(items[2], bool_names);
            }
            return false;
        },
    }
}

fn sexprToNode(alloc: Allocator, e: SExpr) !*constraint.Node {
    switch (e) {
        .atom => |a| {
            const n = try alloc.create(constraint.Node);
            n.* = .{ .lit = try toUvlName(alloc, a) };
            return n;
        },
        .list => |items| {
            const head = items[0].atom;
            if (std.mem.eql(u8, head, "not")) {
                const inner = try sexprToNode(alloc, items[1]);
                const n = try alloc.create(constraint.Node);
                n.* = .{ .not = inner };
                return n;
            }
            const a = try sexprToNode(alloc, items[1]);
            const b = try sexprToNode(alloc, items[2]);
            const n = try alloc.create(constraint.Node);
            if (std.mem.eql(u8, head, "and")) {
                n.* = .{ .and_ = .{ a, b } };
            } else if (std.mem.eql(u8, head, "or")) {
                n.* = .{ .or_ = .{ a, b } };
            } else if (std.mem.eql(u8, head, "=>")) {
                n.* = .{ .implies = .{ a, b } };
            } else {
                n.* = .{ .equiv = .{ a, b } };
            }
            return n;
        },
    }
}

const UvlError = error{Unsupported} || Allocator.Error;

/// Best-effort conversion of a non-pure-boolean SMT-LIB expression back
/// into UVL constraint syntax, for the fixed set of operators the writer
/// itself ever produces outside an aggregate expansion. Returns
/// `error.Unsupported` for anything else (`ite`, `to_int`, `str.len`,
/// `str.++`, ...) -- there is no UVL syntax for these, so the caller
/// drops the whole containing assert rather than emit invalid UVL.
const InfixOp = struct { smt: []const u8, uvl: []const u8 };

/// SMT-LIB operator -> UVL infix text, for every n-ary operator the
/// writer (smt.zig) ever produces outside an aggregate expansion. `not`
/// and unary `-` are handled separately below (prefix, not infix).
const infix_ops = [_]InfixOp{
    .{ .smt = "and", .uvl = " & " },
    .{ .smt = "or", .uvl = " | " },
    .{ .smt = "=>", .uvl = " => " },
    .{ .smt = "=", .uvl = " == " },
    .{ .smt = "distinct", .uvl = " != " },
    .{ .smt = "<", .uvl = " < " },
    .{ .smt = "<=", .uvl = " <= " },
    .{ .smt = ">", .uvl = " > " },
    .{ .smt = ">=", .uvl = " >= " },
    .{ .smt = "+", .uvl = " + " },
    .{ .smt = "-", .uvl = " - " },
    .{ .smt = "*", .uvl = " * " },
    .{ .smt = "/", .uvl = " / " },
};

fn infixOpText(head: []const u8) ?[]const u8 {
    for (infix_ops) |op| {
        if (std.mem.eql(u8, op.smt, head)) return op.uvl;
    }
    return null;
}

fn sexprToUvl(alloc: Allocator, e: SExpr) UvlError![]const u8 {
    switch (e) {
        .atom => |a| {
            if (a.len >= 2 and (a[0] == '"' or a[0] == '|')) return try toUvlName(alloc, a);
            return stripValSuffix(a);
        },
        .list => |items| {
            if (items.len == 0 or items[0] != .atom) return UvlError.Unsupported;
            const head = items[0].atom;
            if (std.mem.eql(u8, head, "not") and items.len == 2) {
                const inner = try sexprToUvl(alloc, items[1]);
                return std.fmt.allocPrint(alloc, "!{s}", .{inner});
            }
            if (std.mem.eql(u8, head, "-") and items.len == 2) {
                const inner = try sexprToUvl(alloc, items[1]);
                return std.fmt.allocPrint(alloc, "-{s}", .{inner});
            }
            const op = infixOpText(head) orelse return UvlError.Unsupported;
            if (items.len < 3) return UvlError.Unsupported;
            var out = std.ArrayList(u8).empty;
            try out.append(alloc, '(');
            try out.appendSlice(alloc, try sexprToUvl(alloc, items[1]));
            for (items[2..]) |it| {
                try out.appendSlice(alloc, op);
                try out.appendSlice(alloc, try sexprToUvl(alloc, it));
            }
            try out.append(alloc, ')');
            return out.toOwnedSlice(alloc);
        },
    }
}

pub const ParsedSmt = struct {
    parsed: ParsedDimacs,
    extra_constraints: [][]const u8,
};

/// Reads every `declare-const`/`assert` top-level form and builds the
/// same shape `parseDimacs` does (plus any residual, non-flattenable
/// constraints) so the result can feed `recovery.recoverFromParsed`
/// directly.
pub fn parseSmt(alloc: Allocator, text: []const u8) !ParsedSmt {
    const top = try parseTop(alloc, text);

    var id_to_name = std.AutoHashMap(i32, []const u8).init(alloc);
    var name_to_id = std.StringHashMap(i32).init(alloc);
    var bool_names = std.StringHashMap(void).init(alloc);
    var next_id: i32 = 1;

    for (top) |form| {
        if (form != .list or form.list.len != 3) continue;
        if (form.list[0] != .atom or !std.mem.eql(u8, form.list[0].atom, "declare-const")) continue;
        if (form.list[1] != .atom or form.list[2] != .atom) continue;
        if (!std.mem.eql(u8, form.list[2].atom, "Bool")) continue;
        const raw_name = form.list[1].atom;
        const uvl_name = try toUvlName(alloc, raw_name);
        try id_to_name.put(next_id, uvl_name);
        try name_to_id.put(uvl_name, next_id);
        try bool_names.put(raw_name, {});
        next_id += 1;
    }

    // A valid model (the dialect uvl2smt writes) declares at least one
    // Bool const -- the SMT-LIB analogue of UVL's "at least one feature"
    // and DIMACS's "at least a `p` line": rejects non-SMT-LIB-feature-model
    // input (e.g. plain UVL or DIMACS text) instead of silently recovering
    // an empty model.
    if (next_id == 1) return error.NoFeatures;

    var clauses = std.ArrayList([]i32).empty;
    var extra = std.ArrayList([]const u8).empty;

    for (top) |form| {
        if (form != .list or form.list.len != 2) continue;
        if (form.list[0] != .atom or !std.mem.eql(u8, form.list[0].atom, "assert")) continue;
        const body = form.list[1];
        if (isPureBoolean(body, &bool_names)) {
            const node = try sexprToNode(alloc, body);
            const node_clauses = constraint.generateClauses(alloc, &name_to_id, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: any2uvl: skipping an assert referencing an unrecognized feature\n", .{});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| try clauses.append(alloc, c);
        } else {
            const text_out = sexprToUvl(alloc, body) catch |err| switch (err) {
                error.Unsupported => {
                    std.debug.print("Warning: any2uvl: dropping an SMT-LIB assert with no UVL constraint-syntax equivalent\n", .{});
                    continue;
                },
                else => return err,
            };
            try extra.append(alloc, text_out);
        }
    }

    return .{
        .parsed = .{ .id_to_name = id_to_name, .name_to_id = name_to_id, .clauses = clauses },
        .extra_constraints = try extra.toOwnedSlice(alloc),
    };
}

/// Full pipeline: SMT-LIB 2 text -> recovered UVL, reusing the entire
/// DIMACS hierarchy-recovery algorithm via `recovery.recoverFromParsed`.
pub fn recoverFromSmt(
    scratch_alloc: Allocator,
    out_alloc: Allocator,
    smt_text: []const u8,
    optimize: bool,
    by_name: bool,
) ![]const u8 {
    const parsed_smt = try parseSmt(scratch_alloc, smt_text);
    return recovery.recoverFromParsed(
        scratch_alloc,
        out_alloc,
        parsed_smt.parsed,
        optimize,
        by_name,
        parsed_smt.extra_constraints,
    );
}

test "s-expression parser: nested lists and quoted symbols" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const top = try parseTop(alloc, "(declare-const |My Root| Bool)\n(assert (=> A Root))\n");
    try std.testing.expectEqual(@as(usize, 2), top.len);
    try std.testing.expect(top[0] == .list);
    try std.testing.expectEqual(@as(usize, 3), top[0].list.len);
    try std.testing.expectEqualStrings("|My Root|", top[0].list[1].atom);
    try std.testing.expectEqualStrings("=>", top[1].list[1].list[0].atom);
}

test "hierarchy recovered from SMT-LIB round-trips through recoverFromParsed" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const smt =
        \\(declare-const Root Bool)
        \\(declare-const A Bool)
        \\(declare-const B Bool)
        \\(assert Root)
        \\(assert (=> A Root))
        \\(assert (=> Root A))
        \\(assert (=> B Root))
        \\(check-sat)
        \\(get-model)
        \\
    ;
    const out = try recoverFromSmt(alloc, alloc, smt, false, false);
    try std.testing.expect(std.mem.indexOf(u8, out, "Root") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "mandatory") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "A") != null);
}

test "non-boolean assert becomes a residual constraint, not lost" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const smt =
        \\(declare-const Root Bool)
        \\(declare-const Root.Power Int)
        \\(assert Root)
        \\(assert (= Root.Power 10))
        \\(check-sat)
        \\
    ;
    const out = try recoverFromSmt(alloc, alloc, smt, false, false);
    try std.testing.expect(std.mem.indexOf(u8, out, "constraints") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "Root.Power == 10") != null);
}

test "an unsupported ite-involving assert is dropped, not emitted as invalid UVL" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const smt =
        \\(declare-const Root Bool)
        \\(declare-const A Bool)
        \\(declare-const A.Power Int)
        \\(assert Root)
        \\(assert (> (ite A A.Power 0) 3))
        \\(check-sat)
        \\
    ;
    const out = try recoverFromSmt(alloc, alloc, smt, false, false);
    try std.testing.expect(std.mem.indexOf(u8, out, "ite") == null);
}

test "parseSmt rejects input with no Bool declare-const (e.g. non-SMT-LIB or non-UVL-shaped input)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    try std.testing.expectError(error.NoFeatures, parseSmt(alloc, "(declare-const x Int)\n(assert (= x 1))\n"));
}

//! Native SMT-LIB 2 writer (`uvl2smt`), replacing the string-splicing
//! Python implementation (`uvllang/main.py`'s `to_smt()`) for the zig
//! backend with real AST traversal over the constraint.zig `Node`/
//! `ArithNode` tree built in Phase 2. Produces the same overall document
//! shape: feature declarations, string-feature value declarations,
//! attribute declarations/values, root assertion, hierarchy asserts,
//! then boolean/arithmetic constraint asserts, `check-sat`/`get-model`.
//!
//! Several gaps in the Python writer are fixed here since the real AST
//! and z3-checked output make them straightforward to find and fix:
//!   - the 2-arg scoped aggregate form (`sum(Feature, Attr)`, restricted
//!     to `Feature` and its descendants) actually restricts the
//!     aggregation now instead of being silently unhandled;
//!   - `floor`/`ceil` are implemented (via `to_int`) instead of not being
//!     recognized at all;
//!   - typed non-Boolean features (`Integer`/`Real`, not just `String`)
//!     get a `_val` companion const, so a comparison against a typed
//!     feature (e.g. the paper's own `sum(Power) < Watt` example, `Watt`
//!     an `Integer` feature) type-checks instead of comparing against the
//!     feature's own `Bool` selection variable;
//!   - a UVL-quoted feature/attribute name (`"My Feature"`) is rewritten
//!     into a valid SMT-LIB symbol (bare if safe, `|...|`-quoted
//!     otherwise) instead of being emitted with its literal quote
//!     characters, which SMT-LIB's `<symbol>` grammar rejects;
//!   - an attribute's declared SMT sort is inferred from its actual
//!     value's shape (a quoted value -> `String`, a value containing `.`
//!     -> `Real`, otherwise `Int`) instead of unconditionally `Int`,
//!     which mismatched a string-valued attribute like `{tag 'v'}` against
//!     the declared sort.

const std = @import("std");
const Allocator = std.mem.Allocator;
const builder_mod = @import("builder");
const constraint = @import("constraint");
const parser = @import("parser");
const Builder = builder_mod.Builder;

fn isOptional(b: *const Builder, name: []const u8) bool {
    if (b.root) |r| {
        if (std.mem.eql(u8, r, name)) return false;
    }
    if (b.hierarchy.get(name)) |info| {
        if (info.parent) |p| {
            if (b.hierarchy.get(p)) |pinfo| {
                for (pinfo.children.items) |edge| {
                    if (std.mem.eql(u8, edge.name, name)) return edge.kind == .optional;
                }
            }
        }
    }
    // Matches uvllang.main.UVL._is_feature_optional's implicit fallthrough
    // (no matching child found -> Python's bare `return` at function end
    // is `None`, falsy) -- practically unreachable for a well-formed tree.
    return false;
}

/// Returns the SMT-LIB sort a feature's declared UVL type needs a value
/// companion const for -- "Boolean" (or untyped) needs none, since the
/// feature's own selection variable already *is* its value.
fn valueSort(feature_type: ?[]const u8) ?[]const u8 {
    const t = feature_type orelse return null;
    if (std.mem.eql(u8, t, "String")) return "String";
    if (std.mem.eql(u8, t, "Integer")) return "Int";
    if (std.mem.eql(u8, t, "Real")) return "Real";
    return null;
}

/// Infers the SMT-LIB sort of a value-attribute's raw text: a quoted
/// literal is a String, an unquoted one containing `.` is a Real,
/// anything else is an Int. Best-effort -- if the same attribute key
/// holds values of different shapes on different features (a modeling
/// inconsistency), the first occurrence found wins the declared sort and
/// a later mismatched assert is a genuine type error z3 will report.
fn inferValueSort(value: []const u8) []const u8 {
    if (value.len > 0 and (value[0] == '\'' or value[0] == '"')) return "String";
    if (std.mem.indexOfScalar(u8, value, '.') != null) return "Real";
    return "Int";
}

fn getAttribute(b: *const Builder, feature: []const u8, key: []const u8) ?[]const u8 {
    const info = b.hierarchy.get(feature) orelse return null;
    for (info.attributes.items) |a| {
        if (std.mem.eql(u8, a.key, key)) return a.value;
    }
    return null;
}

/// Converts a UVL numeric-literal token's raw text into an SMT-LIB
/// numeral/decimal: SMT-LIB has no negative-literal syntax (`-3` isn't a
/// valid <numeral>), so a leading `-` is rewritten to the `(- N)` prefix
/// form.
fn writeNumeral(w: *std.Io.Writer, text: []const u8) !void {
    if (text.len > 0 and text[0] == '-') {
        try w.print("(- {s})", .{text[1..]});
    } else {
        try w.writeAll(text);
    }
}

/// Converts a UVL string-literal token's raw text (single- or
/// double-quoted, quotes included) into an SMT-LIB string literal
/// (always double-quoted). Does not attempt to handle embedded quote
/// escaping beyond what the source already contained.
fn writeStringLiteral(w: *std.Io.Writer, text: []const u8) !void {
    if (text.len < 2) {
        try w.print("\"{s}\"", .{text});
        return;
    }
    try w.writeByte('"');
    try w.writeAll(text[1 .. text.len - 1]);
    try w.writeByte('"');
}

/// Strips a UVL quote wrapper (`"..."` or `'...'`) when it spans the
/// entire string -- the common case for a quoted feature/attribute name.
/// A dotted composite with an embedded quoted segment (e.g.
/// `"My Feature".attr`) doesn't start+end with the same quote character
/// and is left as-is; `identSafe`/`emitIdent` below still handle it
/// safely (falling back to `|...|`-quoting the whole messy string), just
/// without stripping the inner quotes cosmetically.
fn stripOuterQuotes(name: []const u8) []const u8 {
    if (name.len >= 2 and (name[0] == '"' or name[0] == '\'') and name[name.len - 1] == name[0]) {
        return name[1 .. name.len - 1];
    }
    return name;
}

fn isSymbolSafeChar(c: u8) bool {
    if (std.ascii.isAlphanumeric(c)) return true;
    return switch (c) {
        '~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/' => true,
        else => false,
    };
}

fn identSafe(name: []const u8) bool {
    if (name.len == 0) return false;
    if (std.ascii.isDigit(name[0])) return false;
    for (name) |c| {
        if (!isSymbolSafeChar(c)) return false;
    }
    return true;
}

/// Emits `text` as a valid SMT-LIB `<symbol>`: bare if it already is one,
/// `|...|`-quoted (SMT-LIB's own escape mechanism, which allows almost
/// any character except `|` and `\`) otherwise.
fn emitIdent(w: *std.Io.Writer, text: []const u8) !void {
    if (identSafe(text)) {
        try w.writeAll(text);
    } else {
        try w.writeByte('|');
        try w.writeAll(text);
        try w.writeByte('|');
    }
}

fn writeFeatureIdent(w: *std.Io.Writer, name: []const u8) !void {
    try emitIdent(w, stripOuterQuotes(name));
}

/// Writes a reference to the identifier that actually carries its value
/// in the emitted SMT: a typed feature's `_val` companion const, or the
/// name itself for anything else (a dotted `Feature.attr` reference, or a
/// plain untyped feature used as a fallback best-effort case).
fn writeRef(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, name: []const u8) !void {
    if (std.mem.indexOfScalar(u8, name, '.') == null) {
        if (b.hierarchy.get(name)) |info| {
            if (valueSort(info.feature_type) != null) {
                const val_name = try std.fmt.allocPrint(alloc, "{s}_val", .{stripOuterQuotes(name)});
                try emitIdent(w, val_name);
                return;
            }
        }
        try writeFeatureIdent(w, name);
        return;
    }
    // A dotted "Feature.attr" reference: emitted as one identifier (dots
    // are symbol-safe), quoted as a whole if either side needed quoting.
    try emitIdent(w, name);
}

fn descendantsOf(alloc: Allocator, b: *const Builder, root: []const u8, out: *std.ArrayList([]const u8)) !void {
    try out.append(alloc, root);
    if (b.hierarchy.get(root)) |info| {
        for (info.children.items) |edge| try descendantsOf(alloc, b, edge.name, out);
    }
}

/// Writes the `+`-folded (sum) or `+`/`+`-ratio (avg) expansion for an
/// aggregate over `attr_name`, scoped to `scope` (and its descendants) if
/// given, else every feature. A feature contributes its value directly if
/// it's mandatory/root (always selected), or `(ite F F.attr 0)` if
/// optional. Falls back to referencing every in-scope feature's
/// (possibly-undeclared) attribute var directly if none of them actually
/// declare the attribute -- matches the "undeclared attribute" fallback
/// the Python writer used, kept for parity on this edge case.
fn writeAggregateSumOrAvg(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, agg: constraint.Aggregate) !void {
    var scope_list = std.ArrayList([]const u8).empty;
    const scope_features: []const []const u8 = blk: {
        if (agg.scope) |s| {
            try descendantsOf(alloc, b, s, &scope_list);
            break :blk scope_list.items;
        }
        break :blk b.ordered_features.items;
    };

    var carriers = std.ArrayList([]const u8).empty;
    for (scope_features) |f| {
        if (getAttribute(b, f, agg.arg) != null) try carriers.append(alloc, f);
    }
    const fallback = carriers.items.len == 0;
    const terms: []const []const u8 = if (fallback) scope_features else carriers.items;

    if (agg.func == .avg) try w.writeAll("(/ ");
    try w.writeAll("(+ ");
    if (terms.len == 0) try w.writeAll("0");
    for (terms) |f| {
        const attr_ident = try std.fmt.allocPrint(alloc, "{s}.{s}", .{ stripOuterQuotes(f), agg.arg });
        if (fallback) {
            try emitIdent(w, attr_ident);
            try w.writeByte(' ');
            continue;
        }
        if (isOptional(b, f)) {
            try w.writeAll("(ite ");
            try writeFeatureIdent(w, f);
            try w.writeByte(' ');
            try emitIdent(w, attr_ident);
            try w.writeAll(" 0) ");
        } else {
            try emitIdent(w, attr_ident);
            try w.writeByte(' ');
        }
    }
    try w.writeAll(")");

    if (agg.func == .avg) {
        try w.writeAll(" (+ ");
        if (terms.len == 0) try w.writeAll("0");
        for (terms) |f| {
            if (isOptional(b, f)) {
                try w.writeAll("(ite ");
                try writeFeatureIdent(w, f);
                try w.writeAll(" 1 0) ");
            } else {
                try w.writeAll("1 ");
            }
        }
        try w.writeAll("))");
    }
}

// anyerror, not the default inferred `!void`: writeArith/writeArithBin
// mutually recurse, and two inferred-error-set functions calling each
// other is an unresolvable dependency loop in Zig -- one side needs a
// concrete error set to break the cycle.
fn writeArithBin(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, op: []const u8, ab: [2]*constraint.ArithNode) anyerror!void {
    try w.print("({s} ", .{op});
    try writeArith(alloc, w, b, ab[0]);
    try w.writeAll(" ");
    try writeArith(alloc, w, b, ab[1]);
    try w.writeAll(")");
}

fn writeArith(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, n: *const constraint.ArithNode) !void {
    switch (n.*) {
        .num => |t| try writeNumeral(w, t),
        .str => |t| try writeStringLiteral(w, t),
        .ref => |name| try writeRef(alloc, w, b, name),
        .add => |ab| try writeArithBin(alloc, w, b, "+", ab),
        .sub => |ab| try writeArithBin(alloc, w, b, "-", ab),
        .mul => |ab| try writeArithBin(alloc, w, b, "*", ab),
        .div => |ab| try writeArithBin(alloc, w, b, "/", ab),
        .aggregate => |agg| switch (agg.func) {
            .sum, .avg => try writeAggregateSumOrAvg(alloc, w, b, agg),
            .len => {
                try w.writeAll("(str.len ");
                try writeRef(alloc, w, b, agg.arg);
                try w.writeAll(")");
            },
            .floor => {
                try w.writeAll("(to_int ");
                try writeRef(alloc, w, b, agg.arg);
                try w.writeAll(")");
            },
            .ceil => {
                // No native ceil in SMT-LIB's Reals_Ints theory: ceil(x)
                // = -floor(-x) = -(to_int (- x)).
                try w.writeAll("(- 0 (to_int (- 0 ");
                try writeRef(alloc, w, b, agg.arg);
                try w.writeAll(")))");
            },
        },
    }
}

fn cmpOpText(op: constraint.CmpOp) []const u8 {
    return switch (op) {
        .eq => "=",
        .lt => "<",
        .le => "<=",
        .gt => ">",
        .ge => ">=",
        .ne => "distinct",
    };
}

// anyerror for the same reason as writeArithBin above (mutual recursion
// with writeNode).
fn writeNodeBin(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, op: []const u8, ab: [2]*constraint.Node) anyerror!void {
    try w.print("({s} ", .{op});
    try writeNode(alloc, w, b, ab[0]);
    try w.writeAll(" ");
    try writeNode(alloc, w, b, ab[1]);
    try w.writeAll(")");
}

fn writeNode(alloc: Allocator, w: *std.Io.Writer, b: *const Builder, n: *const constraint.Node) !void {
    switch (n.*) {
        .lit => |name| try writeRef(alloc, w, b, name),
        .not => |inner| {
            try w.writeAll("(not ");
            try writeNode(alloc, w, b, inner);
            try w.writeAll(")");
        },
        .and_ => |ab| try writeNodeBin(alloc, w, b, "and", ab),
        .or_ => |ab| try writeNodeBin(alloc, w, b, "or", ab),
        .implies => |ab| try writeNodeBin(alloc, w, b, "=>", ab),
        .equiv => |ab| try writeNodeBin(alloc, w, b, "=", ab),
        .cmp => |cmp| {
            try w.print("({s} ", .{cmpOpText(cmp.op)});
            try writeArith(alloc, w, b, cmp.lhs);
            try w.writeAll(" ");
            try writeArith(alloc, w, b, cmp.rhs);
            try w.writeAll(")");
        },
        .invalid => try w.writeAll("true"), // unreachable for a well-formed constraint
    }
}

fn collectDottedFromArith(set: *std.StringHashMap(void), n: *const constraint.ArithNode) !void {
    switch (n.*) {
        .ref => |name| if (std.mem.indexOfScalar(u8, name, '.') != null) try set.put(name, {}),
        .add, .sub, .mul, .div => |ab| {
            try collectDottedFromArith(set, ab[0]);
            try collectDottedFromArith(set, ab[1]);
        },
        .num, .str, .aggregate => {},
    }
}

fn collectDottedFromNode(set: *std.StringHashMap(void), n: *const constraint.Node) !void {
    switch (n.*) {
        .lit => |name| if (std.mem.indexOfScalar(u8, name, '.') != null) try set.put(name, {}),
        .not => |inner| try collectDottedFromNode(set, inner),
        .and_, .or_, .implies, .equiv => |ab| {
            try collectDottedFromNode(set, ab[0]);
            try collectDottedFromNode(set, ab[1]);
        },
        .cmp => |cmp| {
            try collectDottedFromArith(set, cmp.lhs);
            try collectDottedFromArith(set, cmp.rhs);
        },
        .invalid => {},
    }
}

fn lessThanStr(_: void, x: []const u8, y: []const u8) bool {
    return std.mem.lessThan(u8, x, y);
}

/// `(assert (=> lhs rhs))\n`.
fn writeAssertImplies(w: *std.Io.Writer, lhs: []const u8, rhs: []const u8) !void {
    try w.writeAll("(assert (=> ");
    try writeFeatureIdent(w, lhs);
    try w.writeAll(" ");
    try writeFeatureIdent(w, rhs);
    try w.writeAll("))\n");
}

/// `(assert (not (and a b)))\n`.
fn writeAssertExclusion(w: *std.Io.Writer, a: []const u8, b: []const u8) !void {
    try w.writeAll("(assert (not (and ");
    try writeFeatureIdent(w, a);
    try w.writeAll(" ");
    try writeFeatureIdent(w, b);
    try w.writeAll(")))\n");
}

/// `(assert (=> parent (or m1 m2 ...)))\n`.
fn writeAssertGroupOr(w: *std.Io.Writer, parent: []const u8, members: []const []const u8) !void {
    try w.writeAll("(assert (=> ");
    try writeFeatureIdent(w, parent);
    try w.writeAll(" (or");
    for (members) |m| {
        try w.writeByte(' ');
        try writeFeatureIdent(w, m);
    }
    try w.writeAll(")))\n");
}

/// Writes a full SMT-LIB 2 document for the given parse result.
pub fn writeSmt(alloc: Allocator, w: *std.Io.Writer, result: *const parser.ParseResult) !void {
    const b = &result.builder;

    try w.writeAll("; Feature declarations\n");
    for (b.ordered_features.items) |name| {
        try w.writeAll("(declare-const ");
        try writeFeatureIdent(w, name);
        try w.writeAll(" Bool)\n");
    }

    var val_features = std.ArrayList([]const u8).empty;
    for (b.ordered_features.items) |name| {
        const info = b.hierarchy.get(name).?;
        if (valueSort(info.feature_type)) |_| try val_features.append(alloc, name);
    }
    std.mem.sort([]const u8, val_features.items, {}, lessThanStr);
    if (val_features.items.len > 0) {
        try w.writeAll("\n; Typed-feature value declarations\n");
        for (val_features.items) |name| {
            const info = b.hierarchy.get(name).?;
            const val_name = try std.fmt.allocPrint(alloc, "{s}_val", .{stripOuterQuotes(name)});
            try w.writeAll("(declare-const ");
            try emitIdent(w, val_name);
            try w.print(" {s})\n", .{valueSort(info.feature_type).?});
        }
    }

    // Attribute vars: every dotted reference any constraint actually
    // uses, unioned with every feature-declared value attribute (whether
    // referenced or not) -- matches the Python writer's coverage. Sort is
    // inferred per attribute from the first declared value found for it;
    // a constraint-only reference with no matching declared value falls
    // back to Int.
    var attr_sorts = std.StringHashMap([]const u8).init(alloc);
    for (result.constraints) |c| {
        var referenced = std.StringHashMap(void).init(alloc);
        try collectDottedFromNode(&referenced, c.full);
        var it = referenced.keyIterator();
        while (it.next()) |k| {
            if (!attr_sorts.contains(k.*)) try attr_sorts.put(k.*, "Int");
        }
    }
    for (b.ordered_features.items) |name| {
        const info = b.hierarchy.get(name).?;
        for (info.attributes.items) |a| {
            const key = try std.fmt.allocPrint(alloc, "{s}.{s}", .{ name, a.key });
            if (!attr_sorts.contains(key)) try attr_sorts.put(key, inferValueSort(a.value));
        }
    }
    var attr_names = std.ArrayList([]const u8).empty;
    var attr_it = attr_sorts.keyIterator();
    while (attr_it.next()) |k| try attr_names.append(alloc, k.*);
    std.mem.sort([]const u8, attr_names.items, {}, lessThanStr);
    if (attr_names.items.len > 0) {
        try w.writeAll("\n; Attribute declarations\n");
        for (attr_names.items) |name| {
            try w.writeAll("(declare-const ");
            try emitIdent(w, name);
            try w.print(" {s})\n", .{attr_sorts.get(name).?});
        }
    }

    var wrote_attr_asserts = false;
    for (b.ordered_features.items) |name| {
        const info = b.hierarchy.get(name).?;
        for (info.attributes.items) |a| {
            if (!wrote_attr_asserts) {
                try w.writeAll("\n; Attribute value constraints\n");
                wrote_attr_asserts = true;
            }
            const key = try std.fmt.allocPrint(alloc, "{s}.{s}", .{ name, a.key });
            try w.writeAll("(assert (= ");
            try emitIdent(w, key);
            try w.writeAll(" ");
            if (a.value.len > 0 and (a.value[0] == '\'' or a.value[0] == '"')) {
                try writeStringLiteral(w, a.value);
            } else {
                try writeNumeral(w, a.value);
            }
            try w.writeAll("))\n");
        }
    }

    if (b.root) |root| {
        try w.writeAll("\n; Root feature must be selected\n(assert ");
        try writeFeatureIdent(w, root);
        try w.writeAll(")\n");
    }

    try w.writeAll("\n; Hierarchy constraints\n");
    for (b.ordered_features.items) |name| {
        const info = b.hierarchy.get(name).?;
        for (info.children.items) |edge| {
            try writeAssertImplies(w, edge.name, name);
            if (edge.kind == .mandatory) {
                try writeAssertImplies(w, name, edge.name);
            }
        }
        for (info.groups.items) |g| {
            if (g.kind != .or_group and g.kind != .xor_group) continue;
            try writeAssertGroupOr(w, name, g.members.items);
            if (g.kind == .xor_group) {
                for (g.members.items, 0..) |m1, i| {
                    for (g.members.items[i + 1 ..]) |m2| {
                        try writeAssertExclusion(w, m1, m2);
                    }
                }
            }
        }
    }

    if (result.constraints.len > 0) {
        try w.writeAll("\n; Constraints\n");
        for (result.constraints) |c| {
            try w.writeAll("(assert ");
            try writeNode(alloc, w, b, c.full);
            try w.writeAll(")\n");
        }
    }

    try w.writeAll("\n(check-sat)\n(get-model)\n");
}

const lexer = @import("lexer");

fn buildResult(alloc: Allocator, src: []const u8) !parser.ParseResult {
    const tokens = try lexer.tokenize(alloc, src);
    return parser.parseModel(alloc, tokens);
}

test "simple hierarchy + boolean constraint" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        mandatory
        \\            A
        \\        optional
        \\            B
        \\
        \\constraints
        \\    A => B
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();

    try std.testing.expect(std.mem.indexOf(u8, text, "(declare-const Root Bool)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert Root)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (=> A Root))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (=> Root A))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (=> B Root))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (=> A B))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(check-sat)") != null);
}

test "typed feature comparison uses the _val companion const" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        optional
        \\            Integer Watt
        \\
        \\constraints
        \\    Watt > 3
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();

    try std.testing.expect(std.mem.indexOf(u8, text, "(declare-const Watt_val Int)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(> Watt_val 3)") != null);
}

test "or/xor groups render as an or-assert plus pairwise exclusions" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        alternative
        \\            A
        \\            B
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();

    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (=> Root (or A B)))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (not (and A B)))") != null);
}

test "attribute value assertion and sum aggregate expansion" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root {Power 10}
        \\        optional
        \\            A {Power 5}
        \\
        \\constraints
        \\    sum(Power) > 12
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();

    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (= Root.Power 10))") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (= A.Power 5))") != null);
    // Root is mandatory/root -> contributes directly; A is optional -> ite.
    try std.testing.expect(std.mem.indexOf(u8, text, "Root.Power") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(ite A A.Power 0)") != null);
}

test "negative numeral is wrapped in (- n) form" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root
        \\        optional
        \\            Integer X
        \\
        \\constraints
        \\    X > -3
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();
    try std.testing.expect(std.mem.indexOf(u8, text, "(> X_val (- 3))") != null);
}

test "quoted feature name becomes a valid SMT-LIB symbol" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    "My Root"
        \\        optional
        \\            A
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();
    try std.testing.expect(std.mem.indexOf(u8, text, "(declare-const |My Root| Bool)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert |My Root|)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "\"My Root\"") == null);
}

test "string-valued attribute is declared as String, not Int" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const src =
        \\features
        \\    Root {tag 'v1'}
        \\        optional
        \\            A
        \\
    ;
    const result = try buildResult(alloc, src);
    var aw = std.Io.Writer.Allocating.init(alloc);
    try writeSmt(alloc, &aw.writer, &result);
    const text = aw.written();
    try std.testing.expect(std.mem.indexOf(u8, text, "(declare-const Root.tag String)") != null);
    try std.testing.expect(std.mem.indexOf(u8, text, "(assert (= Root.tag \"v1\"))") != null);
}

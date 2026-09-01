const std = @import("std");
const lexer = @import("lexer");
const parser = @import("parser");
const cnf = @import("cnf");
const constraint = @import("constraint");
const subsumption = @import("subsumption");
const recovery = @import("recovery");
const term = @import("term");

fn usage(t: term.Style) void {
    std.debug.print("{s}\n", .{t.bold("usage: uvl2uvl <input.uvl> [output.uvl] [options]")});
    std.debug.print(
        \\
        \\Reads a UVL feature model and writes a semantically equivalent UVL
        \\model back out, preserving the input's feature hierarchy exactly
        \\(same tree, same groups) while dropping any cross-tree constraint
        \\that turns out to be redundant given the hierarchy and the other
        \\constraints. Every surviving constraint is emitted verbatim, in
        \\its original (not-necessarily-CNF) source form. If output.uvl is
        \\omitted, defaults to <input_basename>_reduced.uvl in the current
        \\directory.
        \\
        \\options:
        \\
    , .{});
    t.option("-v, --verbose", 17, "print feature/constraint counts");
    t.option("-h, --help", 17, "show this help");
    std.debug.print(
        \\
        \\A constraint is dropped only when it's *entirely* subsumed away --
        \\every clause it contributes to the underlying CNF is a superset of
        \\some other surviving clause -- so this can only shrink the
        \\constraint list, never rewrite what's kept. Redundancy is checked
        \\via clause-level subsumption (the same equivalence-preserving pass
        \\as `uvl2cnf
    , .{});
    std.debug.print(" {s}", .{t.flag("--simplify")});
    std.debug.print(
        \\`), which is sound but not complete: it will
        \\not catch every semantically redundant constraint, only ones whose
        \\CNF form is a literal superset of some other clause already
        \\present. Constraints that reference a feature attribute or a
        \\numeric comparison can't be translated to CNF at all and are
        \\always kept as-is, since their redundancy can't be checked this way.
        \\
    , .{});
}

fn basename(path: []const u8) []const u8 {
    if (std.mem.lastIndexOfAny(u8, path, "/\\")) |sep| return path[sep + 1 ..];
    return path;
}

fn stripExtension(name: []const u8) []const u8 {
    if (std.mem.lastIndexOfScalar(u8, name, '.')) |dot| return name[0..dot];
    return name;
}

/// Tag used on every hierarchy-derived clause, so it never gets treated as
/// a candidate for "is this constraint fully subsumed?" -- it's not a
/// constraint at all, just context that lets a real constraint be found
/// redundant.
const hierarchy_tag: usize = std.math.maxInt(usize);

pub fn main(init: std.process.Init) !u8 {
    const alloc = init.arena.allocator();
    const io = init.io;
    const t = term.Style.detect(io, init.environ_map);

    const args = try init.minimal.args.toSlice(alloc);

    var in_path: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var verbose = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage(t);
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            verbose = true;
        } else if (in_path == null) {
            in_path = arg;
        } else if (out_path == null) {
            out_path = arg;
        } else {
            usage(t);
            return 1;
        }
    }

    const in_file = in_path orelse {
        usage(t);
        return 1;
    };
    const out_file_name = out_path orelse try std.fmt.allocPrint(
        alloc,
        "{s}_reduced.uvl",
        .{stripExtension(basename(in_file))},
    );

    const source = std.Io.Dir.cwd().readFileAlloc(io, in_file, alloc, .unlimited) catch |err| {
        t.err("could not read '{s}': {t}", .{ in_file, err });
        return 1;
    };

    const tokens = lexer.tokenize(alloc, source) catch |err| {
        t.err("lex failure: {t}", .{err});
        return 1;
    };

    const result = parser.parseModel(alloc, tokens) catch |err| {
        t.err("parse failure: {t}", .{err});
        return 1;
    };

    const b = &result.builder;
    const root_name = b.root orelse {
        t.err("model has no root feature", .{});
        return 1;
    };

    if (verbose) {
        t.stat("Parsed {d} feature(s), {d} constraint(s)", .{ b.features.count(), result.constraints.len });
    }

    // Same Tier 1/3 non-Boolean-construct warnings uvl2cnf prints: these
    // constructs are lost (Tier 1) or ignored (Tier 3) when the hierarchy
    // is round-tripped through Builder.hierarchy today, regardless of this
    // tool -- see README.md#non-boolean-constructs.
    if (b.cardinality_group_count > 0) {
        t.warn("{d} group(s) use a cardinality range ([i..j]); it is not preserved in the output", .{b.cardinality_group_count});
    }
    if (b.constraint_attribute_count > 0) {
        t.warn("{d} feature-local `constraint`/`constraints` attribute(s) were dropped, not converted", .{b.constraint_attribute_count});
    }
    if (b.cardinality_feature_count > 0) {
        t.warn("{d} feature(s) use a clone cardinality range ([i..j]); it is not preserved in the output", .{b.cardinality_feature_count});
    }
    if (b.typed_feature_count > 0) {
        t.info("{d} feature(s) declare a non-Boolean type; preserved as feature attributes are not re-emitted", .{b.typed_feature_count});
    }
    if (b.attributed_feature_count > 0) {
        t.info("{d} feature(s) carry value attributes; these are not re-emitted", .{b.attributed_feature_count});
    }

    var ids = try cnf.assignIds(alloc, &b.features);

    var all_clauses = std.ArrayList([]const i32).empty;
    var tags = std.ArrayList(usize).empty;

    {
        const root_clause = try alloc.alloc(i32, 1);
        root_clause[0] = ids.get(root_name).?;
        try all_clauses.append(alloc, root_clause);
        try tags.append(alloc, hierarchy_tag);
    }
    {
        var hier_clauses = std.ArrayList([]i32).empty;
        try cnf.hierarchyToCnf(alloc, &b.hierarchy, &ids, &hier_clauses);
        for (hier_clauses.items) |c| {
            try all_clauses.append(alloc, c);
            try tags.append(alloc, hierarchy_tag);
        }
    }

    // produced[i] is true iff constraint i contributed at least one clause
    // to `all_clauses` -- only those constraints are eligible to be
    // judged by subsumption; everything else (non-Boolean, or a reference
    // to an unknown feature) is always kept verbatim since we have no
    // clauses to check its redundancy with.
    var produced = try alloc.alloc(bool, result.constraints.len);
    @memset(produced, false);
    // vacuous[i] is true iff constraint i is Boolean-encodable but
    // generateClauses reduced it to zero clauses -- a tautology (e.g.
    // `C => C`) that's already proven to contribute nothing, unconditionally
    // droppable without needing the subsumption pass at all.
    var vacuous = try alloc.alloc(bool, result.constraints.len);
    @memset(vacuous, false);

    var attribute_ref_constraints: usize = 0;
    var comparison_constraints: usize = 0;

    for (result.constraints, 0..) |info, idx| {
        if (info.node) |node| {
            const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: could not convert constraint at line {d}: unknown feature reference\n", .{info.text_line});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| {
                try all_clauses.append(alloc, c);
                try tags.append(alloc, idx);
            }
            if (node_clauses.len > 0) {
                produced[idx] = true;
            } else {
                vacuous[idx] = true;
            }
        } else if (info.saw_dot) {
            attribute_ref_constraints += 1;
        } else if (info.saw_comparison) {
            comparison_constraints += 1;
        }
    }
    if (attribute_ref_constraints > 0) {
        t.info("{d} constraint(s) reference a feature attribute; kept as-is (redundancy not checked)", .{attribute_ref_constraints});
    }
    if (comparison_constraints > 0) {
        t.info("{d} constraint(s) contain a numeric comparison; kept as-is (redundancy not checked)", .{comparison_constraints});
    }

    const simplified = try subsumption.simplifyTagged(alloc, all_clauses.items, tags.items, false);

    var drop = try alloc.alloc(bool, result.constraints.len);
    @memcpy(drop, vacuous);

    if (simplified.unsat) {
        t.warn("formula is UNSAT (constraints are contradictory); skipping redundancy reduction, writing all constraints unchanged", .{});
    } else {
        var survived = std.AutoHashMap(usize, void).init(alloc);
        for (simplified.tags) |tag| {
            if (tag != hierarchy_tag) try survived.put(tag, {});
        }
        for (produced, 0..) |p, idx| {
            if (p and !survived.contains(idx)) drop[idx] = true;
        }
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        t.err("could not create '{s}': {t}", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    const w = &writer.interface;

    try recovery.serializeHierarchy(alloc, w, root_name, &b.hierarchy);

    var kept: usize = 0;
    var first = true;
    for (result.constraints, 0..) |info, idx| {
        if (drop[idx]) continue;
        if (first) {
            try w.writeAll("\n\nconstraints\n");
            first = false;
        }
        try w.writeAll("    ");
        try w.writeAll(std.mem.trim(u8, info.text, " \t\r\n"));
        try w.writeByte('\n');
        kept += 1;
    }
    try w.flush();

    const dropped = result.constraints.len - kept;
    t.success(
        "Saved {s}: {d} constraint(s) kept, {d} dropped as redundant (of {d} total)",
        .{ out_file_name, kept, dropped, result.constraints.len },
    );
    return 0;
}

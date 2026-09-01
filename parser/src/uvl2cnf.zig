const std = @import("std");
const lexer = @import("lexer");
const parser = @import("parser");
const cnf = @import("cnf");
const subsumption = @import("subsumption");
const pipeline = @import("pipeline");
const term = @import("term");

fn usage(t: term.Style) void {
    std.debug.print("{s}\n", .{t.bold("Usage: uvl2cnf <input.uvl> [output.dimacs] [options]")});
    std.debug.print(
        \\
        \\Converts a UVL feature model to CNF in DIMACS format. 
        \\Defaults to ./<input_basename>.dimacs if output.dimacs is omitted.
        \\
        \\Options:
        \\
    , .{});
    t.option("-v, --verbose", 17, "prints statistics");
    t.option("-h, --help", 17, "shows this help");
    t.option("--simplify", 17, "removes redundant/subsumed clauses");
    t.option("--conversion", 17, "converts some non-Boolean constructs instead of dropping them");
    t.option("--loud", 17, "exits with an error instead of warnings when dropping non-Boolean constructs");
    std.debug.print("\n{s}", .{t.flag("--simplify")});
    std.debug.print(
        \\ runs a global subsumption-elimination pass over the
        \\ full clause set (hierarchy + constraints) before writing it out,
        \\ removing redundant/subsumed clauses
        \\
        \\
    , .{});
    std.debug.print("{s}", .{t.flag("--conversion")});
    std.debug.print(
        \\ applies some conversion strategies (Sundermann et al., SPLC'23) instead of dropping
        \\ non-Boolean constructs and constraints. See README.md#non-boolean-constructs for details.
        \\
        \\
    , .{});
    std.debug.print("{s}", .{t.flag("--loud")});
    std.debug.print(
        \\ exits with an error instead of warning that non-Boolean constructs 
        \\ and constraints are being dropped.
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

pub fn main(init: std.process.Init) !u8 {
    const alloc = init.arena.allocator();
    const io = init.io;
    const t = term.Style.detect(io, init.environ_map);

    const args = try init.minimal.args.toSlice(alloc);

    var in_path: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var parse_only = false;
    var do_simplify = false;
    var do_conversion = false;
    var do_loud = false;
    var verbose = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage(t);
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            verbose = true;
        } else if (std.mem.eql(u8, arg, "--parse-only")) {
            parse_only = true;
        } else if (std.mem.eql(u8, arg, "--simplify")) {
            do_simplify = true;
        } else if (std.mem.eql(u8, arg, "--conversion")) {
            do_conversion = true;
        } else if (std.mem.eql(u8, arg, "--loud")) {
            do_loud = true;
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
        "{s}.dimacs",
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

    if (parse_only) return 0;

    if (verbose) {
        t.stat("Parsed {d} feature(s), {d} constraint(s)", .{ result.builder.features.count(), result.constraints.len });
    }

    const built = try pipeline.buildClauses(alloc, &result, do_conversion);
    var ids = built.ids;
    const clauses = built.clauses;

    pipeline.printNonBooleanWarnings(&result.builder, built.counts, do_conversion);

    if (do_loud) {
        const counts = pipeline.mergeNonBooleanCounts(&result.builder, built.counts);
        if (counts.isThreatening(do_conversion)) {
            t.err("{s}: refusing to write a CNF that silently drops a construct above the Boolean language level (see warnings above)", .{t.flag("--loud")});
            return 1;
        }
    }

    const cclauses: []const []const i32 = @ptrCast(clauses.items);
    var out_clauses: []const []const i32 = cclauses;
    if (do_simplify) {
        const simplified = try subsumption.simplify(alloc, cclauses, false);
        if (simplified.removed_by_subsumption > 0) {
            t.info("Removed {d} clause(s) via subsumption", .{simplified.removed_by_subsumption});
        }
        if (simplified.literals_removed_by_ssr > 0) {
            t.info("Removed {d} literal(s) via self-subsuming resolution", .{simplified.literals_removed_by_ssr});
        }
        if (simplified.tautologies_removed > 0) {
            t.info("Removed {d} tautological clause(s)", .{simplified.tautologies_removed});
        }
        if (simplified.unsat) {
            t.warn("formula is UNSAT (constraints are contradictory)", .{});
        }
        out_clauses = simplified.clauses;
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        t.err("could not create '{s}': {t}", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try cnf.writeDimacs(alloc, &writer.interface, &ids, out_clauses);
    try writer.interface.flush();

    if (verbose) {
        t.stat("Wrote {d} variable(s), {d} clause(s)", .{ ids.count(), out_clauses.len });
    }
    t.success("Saved DIMACS to {s}", .{out_file_name});
    return 0;
}

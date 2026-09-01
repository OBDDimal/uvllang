const std = @import("std");
const lexer = @import("lexer");
const parser = @import("parser");
const cnf = @import("cnf");
const subsumption = @import("subsumption");
const pipeline = @import("pipeline");
const term = @import("term");

fn usage(t: term.Style) void {
    std.debug.print("{s}\n", .{t.bold("usage: uvl2cnf <input.uvl> [output.dimacs] [options]")});
    std.debug.print(
        \\
        \\Converts a UVL feature model to CNF in DIMACS format. Lexing,
        \\parsing, CNF generation, and writing the output all run natively
        \\here -- no Python involved. If output.dimacs is omitted, defaults
        \\to <input_basename>.dimacs in the current directory.
        \\
        \\options:
        \\
    , .{});
    t.option("-v, --verbose", 17, "print feature/constraint/clause counts");
    t.option("-h, --help", 17, "show this help");
    t.option("--simplify", 17, "remove redundant/subsumed clauses (see below)");
    t.option("--conversion", 17, "convert group cardinality + feature-local");
    t.option("", 17, "constraint attributes instead of dropping them");
    t.option("--loud", 17, "exit with an error instead of only warning");
    t.option("", 17, "when a construct above the Boolean language");
    t.option("", 17, "level would be dropped (see below)");
    std.debug.print("\n{s}", .{t.flag("--simplify")});
    std.debug.print(
        \\ runs a global subsumption-elimination pass over the
        \\full clause set (hierarchy + constraints) before writing it out,
        \\removing redundant/subsumed clauses at the cost of extra runtime
        \\on large models.
        \\
        \\
    , .{});
    std.debug.print("{s}", .{t.flag("--conversion")});
    std.debug.print(
        \\ applies the UVLParser paper's (Sundermann et al.,
        \\SPLC'23) conversion strategies instead of silently dropping two
        \\above-Boolean constructs: group cardinality ([i..j] groups) is
        \\encoded as enumerated Boolean clauses, and feature-local
        \\`constraint`/`constraints` attributes are extracted as ordinary
        \\constraints. Feature cardinality (clone multiplicity) is not yet
        \\covered -- see README.md#non-boolean-constructs.
        \\
        \\
    , .{});
    std.debug.print("{s}", .{t.flag("--loud")});
    std.debug.print(
        \\ refuses to write a CNF that silently drops a construct
        \\above the Boolean language level (group/feature cardinality,
        \\feature-local constraint attributes, or a dropped
        \\attribute-reference/comparison constraint) --
    , .{});
    std.debug.print(" {s}\n", .{t.flag("--conversion")});
    std.debug.print(
        \\exempts group cardinality and constraint attributes, since those
        \\are actually handled at that point. The warnings print either way.
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

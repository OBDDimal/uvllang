const std = @import("std");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const cnf = @import("cnf.zig");
const subsumption = @import("subsumption.zig");
const pipeline = @import("pipeline.zig");

fn usage() void {
    std.debug.print(
        \\usage: uvl2cnf <input.uvl> [output.dimacs] [-v|--verbose] [--simplify]
        \\
        \\Converts a UVL feature model to CNF in DIMACS format. Lexing,
        \\parsing, CNF generation, and writing the output all run natively
        \\here -- no Python involved.
        \\
        \\If output.dimacs is omitted, defaults to <input_basename>.dimacs
        \\in the current directory.
        \\
        \\--simplify runs a global subsumption-elimination pass over the
        \\full clause set (hierarchy + constraints) before writing it out,
        \\removing redundant/subsumed clauses at the cost of extra runtime
        \\on large models. Off by default.
        \\
        \\--conversion applies the UVLParser paper's (Sundermann et al.,
        \\SPLC'23) conversion strategies instead of silently dropping two
        \\above-Boolean constructs: group cardinality ([i..j] groups) is
        \\encoded as enumerated Boolean clauses, and feature-local
        \\`constraint`/`constraints` attributes are extracted as ordinary
        \\constraints. Feature cardinality (clone multiplicity) is not yet
        \\covered -- see docs/non_boolean_support.md. Off by default.
        \\
        \\--strict exits with an error instead of writing a CNF that
        \\silently drops a construct above the Boolean language level
        \\(group/feature cardinality, feature-local constraint attributes,
        \\or a dropped attribute-reference/comparison constraint) --
        \\--conversion exempts group cardinality and constraint attributes,
        \\since those are actually handled at that point. Off by default
        \\(the warnings below print either way).
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

    const args = try init.minimal.args.toSlice(alloc);

    var in_path: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var parse_only = false;
    var do_simplify = false;
    var do_conversion = false;
    var do_strict = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage();
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            // Accepted for CLI-convention compatibility: ignored/tautology
            // info is already printed unconditionally below, there's no
            // extra verbose-only detail to gate on this.
        } else if (std.mem.eql(u8, arg, "--parse-only")) {
            parse_only = true;
        } else if (std.mem.eql(u8, arg, "--simplify")) {
            do_simplify = true;
        } else if (std.mem.eql(u8, arg, "--conversion")) {
            do_conversion = true;
        } else if (std.mem.eql(u8, arg, "--strict")) {
            do_strict = true;
        } else if (in_path == null) {
            in_path = arg;
        } else if (out_path == null) {
            out_path = arg;
        } else {
            usage();
            return 1;
        }
    }

    const in_file = in_path orelse {
        usage();
        return 1;
    };
    const out_file_name = out_path orelse try std.fmt.allocPrint(
        alloc,
        "{s}.dimacs",
        .{stripExtension(basename(in_file))},
    );

    const source = std.Io.Dir.cwd().readFileAlloc(io, in_file, alloc, .unlimited) catch |err| {
        std.debug.print("error: could not read '{s}': {t}\n", .{ in_file, err });
        return 1;
    };

    const tokens = lexer.tokenize(alloc, source) catch |err| {
        std.debug.print("error: lex failure: {t}\n", .{err});
        return 1;
    };

    const result = parser.parseModel(alloc, tokens) catch |err| {
        std.debug.print("error: parse failure: {t}\n", .{err});
        return 1;
    };

    if (parse_only) return 0;

    const built = try pipeline.buildClauses(alloc, &result, do_conversion);
    var ids = built.ids;
    const clauses = built.clauses;

    pipeline.printNonBooleanWarnings(&result.builder, built.counts, do_conversion);

    if (do_strict) {
        const counts = pipeline.mergeNonBooleanCounts(&result.builder, built.counts);
        if (counts.isThreatening(do_conversion)) {
            std.debug.print("error: --strict: refusing to write a CNF that silently drops a construct above the Boolean language level (see warnings above)\n", .{});
            return 1;
        }
    }

    const cclauses: []const []const i32 = @ptrCast(clauses.items);
    var out_clauses: []const []const i32 = cclauses;
    if (do_simplify) {
        const simplified = try subsumption.simplify(alloc, cclauses, false);
        if (simplified.removed_by_subsumption > 0) {
            std.debug.print("Info: Removed {d} clause(s) via subsumption\n", .{simplified.removed_by_subsumption});
        }
        if (simplified.literals_removed_by_ssr > 0) {
            std.debug.print("Info: Removed {d} literal(s) via self-subsuming resolution\n", .{simplified.literals_removed_by_ssr});
        }
        if (simplified.tautologies_removed > 0) {
            std.debug.print("Info: Removed {d} tautological clause(s)\n", .{simplified.tautologies_removed});
        }
        if (simplified.unsat) {
            std.debug.print("Warning: formula is UNSAT (constraints are contradictory)\n", .{});
        }
        out_clauses = simplified.clauses;
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        std.debug.print("error: could not create '{s}': {t}\n", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try cnf.writeDimacs(alloc, &writer.interface, &ids, out_clauses);
    try writer.interface.flush();

    std.debug.print("Saved DIMACS to {s}\n", .{out_file_name});
    return 0;
}

test {
    _ = @import("lexer.zig");
    _ = @import("builder.zig");
    _ = @import("constraint.zig");
    _ = @import("cnf.zig");
}

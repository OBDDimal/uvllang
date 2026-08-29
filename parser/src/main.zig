const std = @import("std");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const cnf = @import("cnf.zig");
const constraint = @import("constraint.zig");

fn usage() void {
    std.debug.print(
        \\usage: uvl2cnf <input.uvl> [output.dimacs] [-v|--verbose]
        \\
        \\Converts a UVL feature model to CNF in DIMACS format. Lexing,
        \\parsing, CNF generation, and writing the output all run natively
        \\here -- no Python involved.
        \\
        \\If output.dimacs is omitted, defaults to <input_basename>.dimacs
        \\in the current directory.
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

    var ids = try cnf.assignIds(alloc, &result.builder.features);

    var clauses = std.ArrayList([]i32).empty;

    if (result.builder.root) |root| {
        const clause = try alloc.alloc(i32, 1);
        clause[0] = ids.get(root).?;
        try clauses.append(alloc, clause);
    }

    try cnf.hierarchyToCnf(alloc, &result.builder.hierarchy, &ids, &clauses);

    var attribute_ref_constraints: usize = 0;
    var comparison_constraints: usize = 0;
    for (result.constraints) |info| {
        if (info.node) |node| {
            const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: could not convert constraint at line {d}: unknown feature reference\n", .{info.text_line});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| try clauses.append(alloc, c);
        } else if (info.saw_dot) {
            std.debug.print("Info: Skipping constraint with attribute reference (line {d})\n", .{info.text_line});
            attribute_ref_constraints += 1;
        } else if (info.saw_comparison and info.saw_bool_op) {
            std.debug.print("Info: Skipping constraint with arithmetic comparison (line {d})\n", .{info.text_line});
            comparison_constraints += 1;
        } else if (info.saw_comparison) {
            std.debug.print("Info: Skipping constraint (line {d}): a bare comparison isn't Boolean-encodable\n", .{info.text_line});
            comparison_constraints += 1;
        }
    }
    if (attribute_ref_constraints > 0) {
        std.debug.print("Info: Ignored {d} constraint(s) referencing a feature attribute\n", .{attribute_ref_constraints});
    }
    if (comparison_constraints > 0) {
        std.debug.print("Info: Ignored {d} constraint(s) containing a numeric comparison\n", .{comparison_constraints});
    }

    const b = &result.builder;
    if (b.cardinality_group_count > 0) {
        std.debug.print("Warning: {d} group(s) use a cardinality range ([i..j]); the bound is not enforced in the CNF\n", .{b.cardinality_group_count});
    }
    if (b.constraint_attribute_count > 0) {
        std.debug.print("Warning: {d} feature-local `constraint`/`constraints` attribute(s) were dropped, not converted\n", .{b.constraint_attribute_count});
    }
    if (b.cardinality_feature_count > 0) {
        std.debug.print("Warning: {d} feature(s) use a clone cardinality range ([i..j]); clone instances are not encoded\n", .{b.cardinality_feature_count});
    }
    if (b.typed_feature_count > 0) {
        std.debug.print("Info: {d} feature(s) declare a non-Boolean type; ignored for CNF purposes\n", .{b.typed_feature_count});
    }
    if (b.attributed_feature_count > 0) {
        std.debug.print("Info: {d} feature(s) carry value attributes; ignored for CNF purposes\n", .{b.attributed_feature_count});
    }

    const deduped = try constraint.dedupExact(alloc, clauses.items);
    if (deduped.len < clauses.items.len) {
        std.debug.print("Info: Removed {d} duplicate clause(s)\n", .{clauses.items.len - deduped.len});
    }

    var kept = std.ArrayList([]const i32).empty;
    var n_taut: usize = 0;
    for (deduped) |c| {
        if (cnf.isTautological(c)) {
            n_taut += 1;
            continue;
        }
        try kept.append(alloc, c);
    }
    if (n_taut > 0) {
        std.debug.print("Info: Removed {d} tautological clauses\n", .{n_taut});
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        std.debug.print("error: could not create '{s}': {t}\n", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try cnf.writeDimacs(alloc, &writer.interface, &ids, kept.items);
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

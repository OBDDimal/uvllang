const std = @import("std");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const cnf = @import("cnf.zig");
const constraint = @import("constraint.zig");

fn usage() void {
    std.debug.print("usage: uvlparse <input.uvl> <output.dimacs>\n", .{});
}

pub fn main(init: std.process.Init) !u8 {
    const alloc = init.arena.allocator();
    const io = init.io;

    const args = try init.minimal.args.toSlice(alloc);
    if (args.len < 3) {
        usage();
        return 1;
    }
    const in_path = args[1];
    const out_path = args[2];
    const parse_only = args.len > 3 and std.mem.eql(u8, args[3], "--parse-only");

    const source = std.Io.Dir.cwd().readFileAlloc(io, in_path, alloc, .unlimited) catch |err| {
        std.debug.print("error: could not read '{s}': {t}\n", .{ in_path, err });
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

    var arithmetic_only: usize = 0;
    for (result.constraints) |info| {
        if (info.node) |node| {
            const node_clauses = constraint.generateClauses(alloc, &ids, node) catch |err| switch (err) {
                error.UnknownFeature => {
                    std.debug.print("Warning: could not convert constraint at line {d}: unknown feature reference\n", .{info.text_line});
                    continue;
                },
                error.TooComplex => {
                    std.debug.print("Warning: could not convert constraint at line {d}: too complex to encode exactly within budget\n", .{info.text_line});
                    continue;
                },
                else => return err,
            };
            for (node_clauses) |c| try clauses.append(alloc, c);
        } else if (info.saw_dot) {
            std.debug.print("Info: Skipping constraint with attribute reference (line {d})\n", .{info.text_line});
        } else if (info.saw_comparison and info.saw_bool_op) {
            std.debug.print("Info: Skipping constraint with arithmetic comparison (line {d})\n", .{info.text_line});
        } else {
            arithmetic_only += 1;
        }
    }
    if (arithmetic_only > 0) {
        std.debug.print("Info: Ignored {d} arithmetic constraints\n", .{arithmetic_only});
    }

    var kept = std.ArrayList([]const i32).empty;
    var n_taut: usize = 0;
    for (clauses.items) |c| {
        if (cnf.isTautological(c)) {
            n_taut += 1;
            continue;
        }
        try kept.append(alloc, c);
    }
    if (n_taut > 0) {
        std.debug.print("Info: Removed {d} tautological clauses\n", .{n_taut});
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_path, .{}) catch |err| {
        std.debug.print("error: could not create '{s}': {t}\n", .{ out_path, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try cnf.writeDimacs(alloc, &writer.interface, &ids, kept.items);
    try writer.interface.flush();

    return 0;
}

test {
    _ = @import("lexer.zig");
    _ = @import("builder.zig");
    _ = @import("constraint.zig");
    _ = @import("cnf.zig");
}

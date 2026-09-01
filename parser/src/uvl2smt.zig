const std = @import("std");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const smt = @import("smt.zig");

fn usage() void {
    std.debug.print(
        \\usage: uvl2smt <input.uvl> [output.smt2] [-v|--verbose]
        \\
        \\Converts a UVL feature model to SMT-LIB 2 format. Lexing, parsing,
        \\and SMT generation all run natively here -- no Python involved.
        \\Unlike uvl2cnf, this is not restricted to the plain Boolean
        \\language level: numeric comparisons, aggregate functions
        \\(sum/avg/len/floor/ceil, including the 2-argument scoped form),
        \\and typed (String/Integer/Real) features are all represented.
        \\
        \\Feature-local `constraint`/`constraints` attributes are not
        \\included (matching uvl2cnf's default; see --conversion there for
        \\the CNF-only equivalent) -- only the top-level `constraints`
        \\block is written.
        \\
        \\If output.smt2 is omitted, defaults to <input_basename>.smt2 in
        \\the current directory.
        \\
        \\Note: this replaces the legacy `uvl2smt --antlr`/Lark-backed CLI
        \\tool. That functionality is still available programmatically via
        \\`UVL(backend="lark"/"antlr").to_smt()` in the Python API.
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

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage();
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            // accepted for CLI-convention compatibility; nothing extra to gate on it
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
        "{s}.smt2",
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

    if (result.builder.root == null) {
        std.debug.print("error: model has no root feature\n", .{});
        return 1;
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        std.debug.print("error: could not create '{s}': {t}\n", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try smt.writeSmt(alloc, &writer.interface, &result);
    try writer.interface.flush();

    std.debug.print("Saved SMT-LIB 2 to {s}\n", .{out_file_name});
    return 0;
}

test {
    _ = @import("lexer.zig");
    _ = @import("builder.zig");
    _ = @import("constraint.zig");
    _ = @import("smt.zig");
}

const std = @import("std");
const lexer = @import("lexer");
const parser = @import("parser");
const smt = @import("smt_writer");
const term = @import("term");

fn usage(t: term.Style) void {
    std.debug.print("{s}\n", .{t.bold("Usage: uvl2smt <input.uvl> [output.smt2] [options]")});
    std.debug.print(
        \\
        \\Converts a UVL feature model to SMT-LIB 2 format.
        \\Unlike uvl2cnf, this is neither restricted to the Boolean language level nor requires conversion.
        \\Defaults to ./<input_basename>.smt2 if output.smt2 is omitted.
        \\
        \\Options:
        \\
    , .{});
    t.option("-v, --verbose", 17, "prints feature/constraint counts");
    t.option("-h, --help", 17, "shows this help");
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
        "{s}.smt2",
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

    if (result.builder.root == null) {
        t.err("model has no root feature", .{});
        return 1;
    }

    if (verbose) {
        t.stat("Parsed {d} feature(s), {d} constraint(s) ({d} feature-local)", .{
            result.builder.features.count(),
            result.constraints.len + result.builder.feature_local_constraints.items.len,
            result.builder.feature_local_constraints.items.len,
        });
    }

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        t.err("could not create '{s}': {t}", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try smt.writeSmt(alloc, &writer.interface, &result);
    try writer.interface.flush();

    if (verbose) {
        if (out_file.stat(io) catch null) |s| {
            t.stat("Wrote {d} byte(s) of SMT-LIB 2", .{s.size});
        }
    }
    t.success("Saved SMT-LIB 2 to {s}", .{out_file_name});
    return 0;
}

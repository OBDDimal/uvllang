const std = @import("std");
const recovery = @import("recovery.zig");
const smtlib = @import("smtlib.zig");

fn usage() void {
    std.debug.print(
        \\usage: any2uvl <input.dimacs|input.smt2> [output.uvl] [-v|--verbose]
        \\                [--optimize] [--byname] [--verify] [--propagate]
        \\
        \\Recovers a UVL feature model from a DIMACS CNF file or an SMT-LIB 2
        \\file (the dialect uvl2smt itself writes -- not general SMT-LIB 2;
        \\see parser/src/smtlib.zig). Input format is detected from content,
        \\not the file extension. Lexing, parsing, and recovery all run
        \\natively here -- no Python involved.
        \\
        \\Hierarchy is reconstructed via a spanning-tree heuristic over the
        \\formula's binary implications and group clauses; remaining clauses
        \\(or, for SMT-LIB input, any assert that isn't a pure Boolean
        \\formula over declared features) become cross-tree constraints. The
        \\output is always logically equivalent to the input regardless of
        \\hierarchy-recovery quality.
        \\
        \\--optimize runs a greedy CTC-reduction pass after the initial
        \\recovery, re-parenting features to shrink the residual constraint
        \\count.
        \\--byname breaks equally-shallow parent ties by feature-name
        \\similarity (only affects --optimize).
        \\--verify reparses the written UVL and confirms it round-trips to
        \\an exact-clause-set-equivalent CNF. DIMACS input only -- ignored
        \\(with a warning) for SMT-LIB input. Combined with --optimize, a
        \\FAIL(missing=N, extra=0) result can be a false positive (the
        \\optimizer's subsumption cleanup can legitimately shrink the
        \\clause set to a logically-but-not-syntactically-equivalent
        \\subset) -- a real defect vs. this pattern can only be told apart
        \\with a SAT-based check, which this binary doesn't perform.
        \\--propagate enables an experimental, more expensive unit-propagation-
        \\based implication-recovery pass (see recovery.zig).
        \\
        \\If output.uvl is omitted, defaults to <input_basename>_recovered.uvl
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

const Format = enum { dimacs, smtlib };

/// Sniffs the input format from its first meaningful byte rather than the
/// file extension: DIMACS starts with a `c`/`p` header line or a bare
/// literal, SMT-LIB 2 is s-expressions and so always starts with `(` --
/// once any leading whitespace *and* `;`-prefixed comment lines (which
/// smt.zig's writer always opens with) are skipped over.
fn sniffFormat(source: []const u8) Format {
    var i: usize = 0;
    while (i < source.len) {
        const c = source[i];
        if (c == ' ' or c == '\t' or c == '\r' or c == '\n') {
            i += 1;
            continue;
        }
        if (c == ';') {
            while (i < source.len and source[i] != '\n') i += 1;
            continue;
        }
        return if (c == '(') .smtlib else .dimacs;
    }
    return .dimacs;
}

pub fn main(init: std.process.Init) !u8 {
    const alloc = init.arena.allocator();
    const io = init.io;

    const args = try init.minimal.args.toSlice(alloc);

    var in_path: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var optimize = false;
    var by_name = false;
    var verify = false;
    var propagate = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage();
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            // accepted for CLI-convention compatibility
        } else if (std.mem.eql(u8, arg, "--optimize")) {
            optimize = true;
        } else if (std.mem.eql(u8, arg, "--byname")) {
            by_name = true;
        } else if (std.mem.eql(u8, arg, "--verify")) {
            verify = true;
        } else if (std.mem.eql(u8, arg, "--propagate")) {
            propagate = true;
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
        "{s}_recovered.uvl",
        .{stripExtension(basename(in_file))},
    );

    const source = std.Io.Dir.cwd().readFileAlloc(io, in_file, alloc, .unlimited) catch |err| {
        std.debug.print("error: could not read '{s}': {t}\n", .{ in_file, err });
        return 1;
    };

    const format = sniffFormat(source);

    const out_text = switch (format) {
        .dimacs => recovery.recover(alloc, alloc, source, optimize, by_name, propagate) catch |err| {
            std.debug.print("error: recovery failed: {t}\n", .{err});
            return 1;
        },
        .smtlib => smtlib.recoverFromSmt(alloc, alloc, source, optimize, by_name, propagate) catch |err| {
            std.debug.print("error: recovery failed: {t}\n", .{err});
            return 1;
        },
    };

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        std.debug.print("error: could not create '{s}': {t}\n", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try writer.interface.writeAll(out_text);
    try writer.interface.flush();

    std.debug.print("Saved UVL to {s}\n", .{out_file_name});

    if (verify) {
        if (format == .dimacs) {
            const parsed = recovery.parseDimacs(alloc, source) catch |err| {
                std.debug.print("error: could not re-parse input for --verify: {t}\n", .{err});
                return 1;
            };
            const vr = try recovery.verifyRecovery(alloc, out_text, parsed.clauses.items);
            if (vr.pass()) {
                std.debug.print("any2uvl: DIMACS PASS ({d} clauses)\n", .{vr.total_orig_clauses});
            } else {
                std.debug.print("any2uvl: DIMACS check FAIL: missing={d} extra={d}\n", .{ vr.missing, vr.extra });
                if (optimize and vr.extra == 0) {
                    std.debug.print(
                        "  Note: --optimize's residual-CTC subsumption cleanup can legitimately\n" ++
                        "  make the recovered clause set a syntactically smaller, logically\n" ++
                        "  equivalent subset (missing>0, extra=0 is this pattern) -- this exact\n" ++
                        "  clause-set check can't tell that apart from a real defect without a\n" ++
                        "  SAT solver; see recovery.verifyRecovery's doc comment.\n",
                        .{},
                    );
                }
            }
        } else {
            std.debug.print("Warning: --verify is not supported for SMT-LIB input; skipped\n", .{});
        }
    }

    return 0;
}

test {
    _ = @import("lexer.zig");
    _ = @import("recovery.zig");
    _ = @import("smtlib.zig");
}

test "sniffFormat: DIMACS header and comment lines" {
    try std.testing.expectEqual(Format.dimacs, sniffFormat("p cnf 2 2\n1 0\n"));
    try std.testing.expectEqual(Format.dimacs, sniffFormat("c 1 Root\np cnf 1 1\n1 0\n"));
    try std.testing.expectEqual(Format.dimacs, sniffFormat("  \n  c 1 Root\n1 0\n"));
}

test "sniffFormat: SMT-LIB s-expressions, including after a leading comment" {
    try std.testing.expectEqual(Format.smtlib, sniffFormat("(declare-const A Bool)\n"));
    try std.testing.expectEqual(Format.smtlib, sniffFormat("; Feature declarations\n(declare-const A Bool)\n"));
    try std.testing.expectEqual(Format.smtlib, sniffFormat("\n\n  ; a comment\n; another\n(assert A)\n"));
}

test "sniffFormat: empty or all-comment input defaults to dimacs" {
    try std.testing.expectEqual(Format.dimacs, sniffFormat(""));
    try std.testing.expectEqual(Format.dimacs, sniffFormat("   \n  "));
    try std.testing.expectEqual(Format.dimacs, sniffFormat("; only a comment\n"));
}

test "verifyRecovery: matching hierarchy reports zero missing/extra" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Same ids/clauses a real uvl2cnf-produced DIMACS + its any2uvl
    // recovery would agree on: A=1, Root=2 (alphabetical).
    var clauses = std.ArrayList([]i32).empty;
    try clauses.append(alloc, try alloc.dupe(i32, &[_]i32{2}));
    try clauses.append(alloc, try alloc.dupe(i32, &[_]i32{ -1, 2 }));

    const uvl_text = "features\n    Root\n        optional\n            A\n";
    const result = try recovery.verifyRecovery(alloc, uvl_text, clauses.items);
    try std.testing.expect(result.pass());
    try std.testing.expectEqual(@as(usize, 2), result.total_orig_clauses);
    try std.testing.expectEqual(@as(usize, 0), result.missing);
    try std.testing.expectEqual(@as(usize, 0), result.extra);
}

test "verifyRecovery: a genuinely different hierarchy reports missing/extra" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Original said A was mandatory (-1 2 AND -2 1); recovered text below
    // only has A optional (-1 2) -- the mandatory direction is missing.
    var clauses = std.ArrayList([]i32).empty;
    try clauses.append(alloc, try alloc.dupe(i32, &[_]i32{2}));
    try clauses.append(alloc, try alloc.dupe(i32, &[_]i32{ -1, 2 }));
    try clauses.append(alloc, try alloc.dupe(i32, &[_]i32{ -2, 1 }));

    const uvl_text = "features\n    Root\n        optional\n            A\n";
    const result = try recovery.verifyRecovery(alloc, uvl_text, clauses.items);
    try std.testing.expect(!result.pass());
    try std.testing.expectEqual(@as(usize, 1), result.missing);
    try std.testing.expectEqual(@as(usize, 0), result.extra);
}

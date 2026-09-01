const std = @import("std");
const recovery = @import("recovery");
const smt_reader = @import("smt_reader");
const term = @import("term");

fn usage(t: term.Style) void {
    std.debug.print("{s}\n", .{t.bold("usage: any2uvl <input.dimacs|input.smt2> [output.uvl] [options]")});
    std.debug.print(
        \\
        \\Recovers a UVL feature model from a DIMACS CNF file or an SMT-LIB 2
        \\file (the dialect uvl2smt itself writes -- not general SMT-LIB 2;
        \\see parser/src/smt/reader.zig). Input format is detected from content,
        \\not the file extension. Lexing, parsing, and recovery all run
        \\natively here -- no Python involved. If output.uvl is omitted,
        \\defaults to <input_basename>_recovered.uvl in the current directory.
        \\
        \\options:
        \\
    , .{});
    t.option("-v, --verbose", 17, "print variable/clause/constraint counts");
    t.option("-h, --help", 17, "show this help");
    t.option("--optimize", 17, "greedy CTC-reduction pass after initial recovery");
    t.option("--byname", 17, "break parent ties by feature-name similarity");
    std.debug.print("  {s:<17}(only affects {s})\n", .{ "", t.flag("--optimize") });
    t.option("--verify", 17, "confirm the output round-trips to an equivalent");
    t.option("", 17, "CNF (DIMACS input only; see below)");
    t.option("--propagate", 17, "experimental unit-propagation-based implication");
    t.option("", 17, "recovery (see recovery.zig)");
    std.debug.print(
        \\
        \\Hierarchy is reconstructed via a spanning-tree heuristic over the
        \\formula's binary implications and group clauses; remaining clauses
        \\(or, for SMT-LIB input, any assert that isn't a pure Boolean
        \\formula over declared features) become cross-tree constraints. The
        \\output is always logically equivalent to the input regardless of
        \\hierarchy-recovery quality.
        \\
        \\
    , .{});
    std.debug.print("{s}", .{t.flag("--verify")});
    std.debug.print(
        \\ reparses the written UVL and confirms it round-trips to
        \\an exact-clause-set-equivalent CNF. Combined with
    , .{});
    std.debug.print(" {s}", .{t.flag("--optimize")});
    std.debug.print(
        \\, a
        \\FAIL(missing=N, extra=0) result can be a false positive (the
        \\optimizer's subsumption cleanup can legitimately shrink the
        \\clause set to a logically-but-not-syntactically-equivalent
        \\subset) -- a real defect vs. this pattern can only be told apart
        \\with a SAT-based check, which this binary doesn't perform.
        \\
    , .{});
}

/// Rough verbose-only input stat for SMT-LIB: counts top-level forms by
/// substring, not a real parse -- good enough for -v, not a source of
/// truth (smt_reader.zig does the actual parsing).
fn countOccurrences(haystack: []const u8, needle: []const u8) usize {
    var count: usize = 0;
    var i: usize = 0;
    while (std.mem.indexOfPos(u8, haystack, i, needle)) |pos| {
        count += 1;
        i = pos + needle.len;
    }
    return count;
}

/// Verbose-only output stat: number of non-empty constraint lines
/// serializeHierarchy's caller appended after the "constraints\n" header
/// (there is none if every constraint was dropped or the model had none).
fn countConstraintLines(uvl_text: []const u8) usize {
    const marker = "\nconstraints\n";
    const start = (std.mem.indexOf(u8, uvl_text, marker) orelse return 0) + marker.len;
    var count: usize = 0;
    var it = std.mem.splitScalar(u8, uvl_text[start..], '\n');
    while (it.next()) |line| {
        if (std.mem.trim(u8, line, " \t\r").len > 0) count += 1;
    }
    return count;
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
    const t = term.Style.detect(io, init.environ_map);

    const args = try init.minimal.args.toSlice(alloc);

    var in_path: ?[]const u8 = null;
    var out_path: ?[]const u8 = null;
    var optimize = false;
    var by_name = false;
    var verify = false;
    var propagate = false;
    var verbose = false;

    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "-h") or std.mem.eql(u8, arg, "--help")) {
            usage(t);
            return 0;
        } else if (std.mem.eql(u8, arg, "-v") or std.mem.eql(u8, arg, "--verbose")) {
            verbose = true;
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
        "{s}_recovered.uvl",
        .{stripExtension(basename(in_file))},
    );

    const source = std.Io.Dir.cwd().readFileAlloc(io, in_file, alloc, .unlimited) catch |err| {
        t.err("could not read '{s}': {t}", .{ in_file, err });
        return 1;
    };

    const format = sniffFormat(source);

    if (verbose) {
        switch (format) {
            .dimacs => {
                const parsed = recovery.parseDimacs(alloc, source) catch |err| {
                    t.err("could not parse DIMACS input: {t}", .{err});
                    return 1;
                };
                t.stat("Read {d} variable(s), {d} clause(s)", .{ parsed.id_to_name.count(), parsed.clauses.items.len });
            },
            .smtlib => {
                t.stat(
                    "Read {d} declared const(s), {d} assert(s)",
                    .{ countOccurrences(source, "(declare-const"), countOccurrences(source, "(assert") },
                );
            },
        }
    }

    const out_text = switch (format) {
        .dimacs => recovery.recover(alloc, alloc, source, optimize, by_name, propagate) catch |err| {
            t.err("recovery failed: {t}", .{err});
            return 1;
        },
        .smtlib => smt_reader.recoverFromSmt(alloc, alloc, source, optimize, by_name, propagate) catch |err| {
            t.err("recovery failed: {t}", .{err});
            return 1;
        },
    };

    var out_file = std.Io.Dir.cwd().createFile(io, out_file_name, .{}) catch |err| {
        t.err("could not create '{s}': {t}", .{ out_file_name, err });
        return 1;
    };
    defer out_file.close(io);
    var buf: [1 << 16]u8 = undefined;
    var writer = out_file.writer(io, &buf);
    try writer.interface.writeAll(out_text);
    try writer.interface.flush();

    if (verbose) {
        t.stat("Wrote {d} constraint(s)", .{countConstraintLines(out_text)});
    }
    t.success("Saved UVL to {s}", .{out_file_name});

    if (verify) {
        if (format == .dimacs) {
            const parsed = recovery.parseDimacs(alloc, source) catch |err| {
                t.err("could not re-parse input for {s}: {t}", .{ t.flag("--verify"), err });
                return 1;
            };
            const vr = try recovery.verifyRecovery(alloc, out_text, parsed.clauses.items);
            if (vr.pass()) {
                t.success("any2uvl: DIMACS PASS ({d} clauses)", .{vr.total_orig_clauses});
            } else {
                t.err("any2uvl: DIMACS check FAIL: missing={d} extra={d}", .{ vr.missing, vr.extra });
                if (optimize and vr.extra == 0) {
                    std.debug.print(
                        "  Note: {s}'s residual-CTC subsumption cleanup can legitimately\n" ++
                        "  make the recovered clause set a syntactically smaller, logically\n" ++
                        "  equivalent subset (missing>0, extra=0 is this pattern) -- this exact\n" ++
                        "  clause-set check can't tell that apart from a real defect without a\n" ++
                        "  SAT solver; see recovery.verifyRecovery's doc comment.\n",
                        .{t.flag("--optimize")},
                    );
                }
            }
        } else {
            t.warn("{s} is not supported for SMT-LIB input; skipped", .{t.flag("--verify")});
        }
    }

    return 0;
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

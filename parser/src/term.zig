//! Minimal ANSI coloring for the 4 CLI tools' own stderr output (usage
//! text, Info:/Warning:/error: lines, the final "Saved ..." line, and
//! -v/--verbose stats). Deliberately not used by pipeline.zig's shared
//! `printNonBooleanWarnings` -- that function is also called from
//! capi.zig (the Python API's backend), and threading terminal detection
//! through the CLI/library-shared pipeline isn't worth the extra surface
//! for output only the CLI path displays directly.
//!
//! Color is used sparingly (a handful of named colors, no 256-color/RGB
//! codes, no styling beyond bold) and only when stderr is a real terminal
//! and the user hasn't opted out via `NO_COLOR` (https://no-color.org).

const std = @import("std");

pub const Style = struct {
    color: bool,

    pub fn detect(io: std.Io, environ: *const std.process.Environ.Map) Style {
        const no_color = environ.get("NO_COLOR") != null;
        const is_tty = std.Io.File.stderr().supportsAnsiEscapeCodes(io) catch false;
        return .{ .color = is_tty and !no_color };
    }

    fn wrap(self: Style, comptime code: []const u8, comptime text: []const u8) []const u8 {
        return if (self.color) "\x1b[" ++ code ++ "m" ++ text ++ "\x1b[0m" else text;
    }

    pub fn bold(self: Style, comptime text: []const u8) []const u8 {
        return self.wrap("1", text);
    }

    /// Cyan, never bold -- every literal flag/option name (`--simplify`,
    /// `-v, --verbose`, ...) is styled this way everywhere it's printed,
    /// in `--help` text and in Info:/Warning:/error: messages alike. Bold
    /// is reserved for the "usage: ..." line only.
    pub fn flag(self: Style, comptime text: []const u8) []const u8 {
        return self.wrap("36", text);
    }

    fn tagged(self: Style, comptime code: []const u8, comptime label: []const u8, comptime fmt: []const u8, args: anytype) void {
        if (self.color) {
            std.debug.print("\x1b[" ++ code ++ "m" ++ label ++ "\x1b[0m " ++ fmt ++ "\n", args);
        } else {
            std.debug.print(label ++ " " ++ fmt ++ "\n", args);
        }
    }

    /// Cyan "Info:" -- routine, expected information (counts, choices made).
    pub fn info(self: Style, comptime fmt: []const u8, args: anytype) void {
        self.tagged("36", "Info:", fmt, args);
    }

    /// Yellow "Warning:" -- something was silently dropped/ignored/degraded.
    pub fn warn(self: Style, comptime fmt: []const u8, args: anytype) void {
        self.tagged("33", "Warning:", fmt, args);
    }

    /// Red "error:" -- the command is about to fail.
    pub fn err(self: Style, comptime fmt: []const u8, args: anytype) void {
        self.tagged("31", "error:", fmt, args);
    }

    /// Green, no label -- the command's own successful outcome line.
    pub fn success(self: Style, comptime fmt: []const u8, args: anytype) void {
        if (self.color) {
            std.debug.print("\x1b[32m" ++ fmt ++ "\x1b[0m\n", args);
        } else {
            std.debug.print(fmt ++ "\n", args);
        }
    }

    /// Dim, no label -- -v/--verbose feature/constraint/clause counts.
    pub fn stat(self: Style, comptime fmt: []const u8, args: anytype) void {
        if (self.color) {
            std.debug.print("\x1b[2m" ++ fmt ++ "\x1b[0m\n", args);
        } else {
            std.debug.print(fmt ++ "\n", args);
        }
    }

    /// One line of a `--help` flag list: `name` (e.g. "-v, --verbose")
    /// styled like `flag` above so it's visually distinct from `desc`,
    /// which stays plain. `width` is the column `desc` starts at, padded
    /// with spaces based on `name`'s own length so padding isn't thrown
    /// off by invisible escape codes -- pass "" for `name` on a
    /// continuation line to align wrapped description text under the
    /// same column.
    pub fn option(self: Style, name: []const u8, width: usize, desc: []const u8) void {
        if (self.color) {
            std.debug.print("  \x1b[36m{s}\x1b[0m", .{name});
        } else {
            std.debug.print("  {s}", .{name});
        }
        var pad: usize = if (name.len < width) width - name.len else 1;
        while (pad > 0) : (pad -= 1) std.debug.print(" ", .{});
        std.debug.print("{s}\n", .{desc});
    }
};

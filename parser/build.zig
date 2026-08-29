const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    // Plain `zig build` (standardOptimizeOption's default) builds Debug --
    // 10-15x slower than ReleaseFast on this codebase, and easy to end up
    // shipping by accident since nothing about the command looks wrong.
    // Ship performance matters here (uvl2cnf execs straight into this
    // binary), so default to ReleaseFast; `-Doptimize=Debug` still opts
    // into safety-checked builds for debugging.
    const optimize = b.option(
        std.builtin.OptimizeMode,
        "optimize",
        "Prioritize performance, safety, or binary size (default: ReleaseFast)",
    ) orelse .ReleaseFast;

    const exe = b.addExecutable(.{
        .name = "uvl2cnf",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(exe);

    const lib = b.addLibrary(.{
        .name = "uvlparser",
        .linkage = .dynamic,
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/capi.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(lib);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run uvl2cnf");
    run_step.dependOn(&run_cmd.step);

    const test_step = b.step("test", "Run unit tests");
    const test_files = [_][]const u8{
        "src/lexer.zig",
        "src/builder.zig",
        "src/parser.zig",
        "src/constraint.zig",
        "src/cnf.zig",
        "src/recovery.zig",
    };
    for (test_files) |file| {
        const t = b.addTest(.{
            .root_module = b.createModule(.{
                .root_source_file = b.path(file),
                .target = target,
                // Always Debug regardless of the exe/lib's optimize mode,
                // to keep safety checks (bounds, overflow, ...) on in tests.
                .optimize = .Debug,
            }),
        });
        const run_t = b.addRunArtifact(t);
        test_step.dependOn(&run_t.step);
    }
}

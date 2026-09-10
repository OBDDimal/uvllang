const std = @import("std");

/// The full internal dependency graph, built once per optimize mode (exe/lib
/// artifacts want `optimize`; tests always want `.Debug`, see `build()`
/// below). Modules are wired together by name via `addImport`, not by
/// relative file path -- a file's directory has no bearing on what it can
/// import; only the edges declared here do. This is the one place the
/// architecture (who depends on whom) is written down.
const Modules = struct {
    term: *std.Build.Module,
    token: *std.Build.Module,
    lexer: *std.Build.Module,
    constraint: *std.Build.Module,
    builder: *std.Build.Module,
    parser: *std.Build.Module,
    cnf: *std.Build.Module,
    subsumption: *std.Build.Module,
    conversion: *std.Build.Module,
    smt_writer: *std.Build.Module,
    smt_reader: *std.Build.Module,
    recovery: *std.Build.Module,
    pipeline: *std.Build.Module,
};

const Import = struct { name: []const u8, module: *std.Build.Module };

fn addImports(mod: *std.Build.Module, imports: []const Import) void {
    for (imports) |i| mod.addImport(i.name, i.module);
}

fn newModule(
    b: *std.Build,
    path: []const u8,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    pyodide: bool,
    imports: []const Import,
) *std.Build.Module {
    const mod = b.createModule(.{
        .root_source_file = b.path(path),
        .target = target,
        .optimize = optimize,
        .single_threaded = pyodide,
        // wasm32-emscripten's dynamic-library ABI (Pyodide's `-Dpyodide=true`
        // path) needs every object PIC to link as a side module; native
        // builds don't use this shared-module scheme and stay unaffected.
        .pic = if (pyodide) true else null,
        // ReleaseFast (the default, see below) doesn't strip debug info on
        // its own the way ReleaseSmall does -- without this, the 4 CLI
        // binaries + libuvlparser.so ship ~27MB of unstripped symbols in a
        // release build for no benefit. `-Doptimize=Debug` (explicitly for
        // debugging) keeps full symbols as usual.
        .strip = optimize != .Debug,
    });
    addImports(mod, imports);
    return mod;
}

fn buildModules(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    pyodide: bool,
) Modules {
    // Leaves first: each module lists only the modules it directly
    // @imports by name in its own source.
    const term = newModule(b, "src/term.zig", target, optimize, pyodide, &.{});
    const token = newModule(b, "src/parse/token.zig", target, optimize, pyodide, &.{});
    const lexer = newModule(b, "src/parse/lexer.zig", target, optimize, pyodide, &.{
        .{ .name = "token", .module = token },
    });
    const constraint = newModule(b, "src/parse/constraint.zig", target, optimize, pyodide, &.{
        .{ .name = "token", .module = token },
        .{ .name = "lexer", .module = lexer },
    });
    const builder = newModule(b, "src/parse/builder.zig", target, optimize, pyodide, &.{
        .{ .name = "constraint", .module = constraint },
    });
    const parser = newModule(b, "src/parse/parser.zig", target, optimize, pyodide, &.{
        .{ .name = "token", .module = token },
        .{ .name = "builder", .module = builder },
        .{ .name = "constraint", .module = constraint },
        .{ .name = "lexer", .module = lexer },
    });
    const cnf = newModule(b, "src/cnf/cnf.zig", target, optimize, pyodide, &.{
        .{ .name = "builder", .module = builder },
    });
    const subsumption = newModule(b, "src/cnf/subsumption.zig", target, optimize, pyodide, &.{});
    const conversion = newModule(b, "src/cnf/conversion.zig", target, optimize, pyodide, &.{
        .{ .name = "builder", .module = builder },
        .{ .name = "constraint", .module = constraint },
    });
    const smt_writer = newModule(b, "src/smt/writer.zig", target, optimize, pyodide, &.{
        .{ .name = "builder", .module = builder },
        .{ .name = "constraint", .module = constraint },
        .{ .name = "parser", .module = parser },
        .{ .name = "lexer", .module = lexer },
    });
    const recovery = newModule(b, "src/recovery.zig", target, optimize, pyodide, &.{
        .{ .name = "builder", .module = builder },
        .{ .name = "cnf", .module = cnf },
        .{ .name = "subsumption", .module = subsumption },
        .{ .name = "lexer", .module = lexer },
        .{ .name = "parser", .module = parser },
        .{ .name = "constraint", .module = constraint },
    });
    const smt_reader = newModule(b, "src/smt/reader.zig", target, optimize, pyodide, &.{
        .{ .name = "recovery", .module = recovery },
        .{ .name = "constraint", .module = constraint },
    });
    const pipeline = newModule(b, "src/pipeline.zig", target, optimize, pyodide, &.{
        .{ .name = "parser", .module = parser },
        .{ .name = "cnf", .module = cnf },
        .{ .name = "constraint", .module = constraint },
        .{ .name = "conversion", .module = conversion },
        .{ .name = "builder", .module = builder },
        .{ .name = "lexer", .module = lexer },
    });

    return .{
        .term = term,
        .token = token,
        .lexer = lexer,
        .constraint = constraint,
        .builder = builder,
        .parser = parser,
        .cnf = cnf,
        .subsumption = subsumption,
        .conversion = conversion,
        .smt_writer = smt_writer,
        .smt_reader = smt_reader,
        .recovery = recovery,
        .pipeline = pipeline,
    };
}

/// Same dependency edges as `buildModules` above, in a form that can be
/// serialized onto a `zig build-lib` command line -- see `buildPyodideLib`.
/// Keep in sync with `buildModules` if the module graph changes.
const ModuleSpec = struct {
    name: []const u8,
    path: []const u8,
    deps: []const []const u8,
};

const capi_deps = [_][]const u8{
    "lexer", "parser", "builder", "cnf", "constraint",
    "subsumption", "recovery", "pipeline", "smt_writer", "conversion",
};

const module_specs = [_]ModuleSpec{
    .{ .name = "lexer", .path = "src/parse/lexer.zig", .deps = &.{"token"} },
    .{ .name = "parser", .path = "src/parse/parser.zig", .deps = &.{ "token", "builder", "constraint", "lexer" } },
    .{ .name = "builder", .path = "src/parse/builder.zig", .deps = &.{"constraint"} },
    .{ .name = "cnf", .path = "src/cnf/cnf.zig", .deps = &.{"builder"} },
    .{ .name = "constraint", .path = "src/parse/constraint.zig", .deps = &.{ "token", "lexer" } },
    .{ .name = "subsumption", .path = "src/cnf/subsumption.zig", .deps = &.{} },
    .{ .name = "recovery", .path = "src/recovery.zig", .deps = &.{ "builder", "cnf", "subsumption", "lexer", "parser", "constraint" } },
    .{ .name = "pipeline", .path = "src/pipeline.zig", .deps = &.{ "parser", "cnf", "constraint", "conversion", "builder", "lexer" } },
    .{ .name = "smt_writer", .path = "src/smt/writer.zig", .deps = &.{ "builder", "constraint", "parser", "lexer" } },
    .{ .name = "conversion", .path = "src/cnf/conversion.zig", .deps = &.{ "builder", "constraint" } },
    .{ .name = "token", .path = "src/parse/token.zig", .deps = &.{} },
};

/// Builds libuvlparser.so for wasm32-emscripten (Pyodide) by invoking `zig
/// build-lib` directly via a Run step, bypassing `b.addLibrary`/
/// `b.installArtifact`. Necessary because wasm-ld's own "-shared" support
/// is explicitly unstable (it prints a warning saying so on every such
/// link) and `zig build`'s Compile step treats any linker stderr it
/// doesn't recognize as a hard failure with no way to allow it -- `zig
/// build-lib` invoked as a plain subprocess isn't subject to that check,
/// and does produce a valid binary despite the warning.
///
/// Also requires two capi.zig-side wasm32-emscripten workarounds (see its
/// comments): `std.heap.smp_allocator` needs real threads Emscripten
/// doesn't have here, and Zig's default debug-I/O backend
/// (`std.Io.Threaded`) depends on a `getrandom` binding `std/posix.zig`
/// doesn't define for the `.emscripten` OS tag.
fn buildPyodideLib(
    b: *std.Build,
    optimize: std.builtin.OptimizeMode,
) void {
    const run = std.Build.Step.Run.create(b, "zig build-lib (pyodide)");
    run.addArg(b.graph.zig_exe);
    run.addArg("build-lib");

    const common = [_][]const u8{
        "-fsingle-threaded",
        "-fPIC",
        b.fmt("-O{s}", .{@tagName(optimize)}),
        "-target",
        "wasm32-emscripten",
    };

    // Root module first, then each dependency module -- order doesn't
    // matter to zig (names are resolved by declaration, not position),
    // this just mirrors the order zig's own `-M`-flag driver produces.
    run.addArgs(&common);
    for (capi_deps) |dep| {
        run.addArg("--dep");
        run.addArg(dep);
    }
    run.addPrefixedFileArg("-Mroot=", b.path("src/capi.zig"));

    for (module_specs) |spec| {
        run.addArgs(&common);
        for (spec.deps) |dep| {
            run.addArg("--dep");
            run.addArg(dep);
        }
        run.addPrefixedFileArg(b.fmt("-M{s}=", .{spec.name}), b.path(spec.path));
    }

    if (b.sysroot) |sysroot| {
        run.addArg("--sysroot");
        run.addArg(sysroot);
    }
    run.addArg("--name");
    run.addArg("uvlparser");
    run.addArg("-dynamic");

    const out = run.addPrefixedOutputFileArg("-femit-bin=", "libuvlparser.so");
    b.getInstallStep().dependOn(&b.addInstallLibFile(out, "libuvlparser.so").step);
}

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

    // Pyodide/wasm32-emscripten only produces libuvlparser.so -- built for
    // ctypes.CDLL inside a Pyodide runtime, loaded the same way _zig.py
    // loads it natively. The 4 CLI binaries don't apply there (no
    // subprocess model in a browser, and Zig's std start code has no
    // wasm32-emscripten entry point at all) and are skipped rather than
    // attempted. wasm32-emscripten's std lib support also does not
    // implement the default multi-threaded allocator/Thread paths this
    // codebase never actually uses, so this target is always built
    // single-threaded.
    const pyodide = b.option(
        bool,
        "pyodide",
        "Build only libuvlparser.so, for wasm32-emscripten (default: false)",
    ) orelse false;

    if (pyodide) {
        buildPyodideLib(b, optimize);
        return;
    }

    const mods = buildModules(b, target, optimize, false);

    const uvl2cnf_mod = newModule(b, "src/uvl2cnf.zig", target, optimize, false, &.{
        .{ .name = "term", .module = mods.term },
        .{ .name = "lexer", .module = mods.lexer },
        .{ .name = "parser", .module = mods.parser },
        .{ .name = "cnf", .module = mods.cnf },
        .{ .name = "subsumption", .module = mods.subsumption },
        .{ .name = "pipeline", .module = mods.pipeline },
        // test-only:
        .{ .name = "builder", .module = mods.builder },
        .{ .name = "constraint", .module = mods.constraint },
    });
    const exe = b.addExecutable(.{ .name = "uvl2cnf", .root_module = uvl2cnf_mod });
    b.installArtifact(exe);

    const uvl2uvl_mod = newModule(b, "src/uvl2uvl.zig", target, optimize, false, &.{
        .{ .name = "term", .module = mods.term },
        .{ .name = "lexer", .module = mods.lexer },
        .{ .name = "parser", .module = mods.parser },
        .{ .name = "cnf", .module = mods.cnf },
        .{ .name = "constraint", .module = mods.constraint },
        .{ .name = "subsumption", .module = mods.subsumption },
        .{ .name = "recovery", .module = mods.recovery },
        // test-only:
        .{ .name = "builder", .module = mods.builder },
    });
    const uvl2uvl_exe = b.addExecutable(.{ .name = "uvl2uvl", .root_module = uvl2uvl_mod });
    b.installArtifact(uvl2uvl_exe);

    const uvl2smt_mod = newModule(b, "src/uvl2smt.zig", target, optimize, false, &.{
        .{ .name = "term", .module = mods.term },
        .{ .name = "lexer", .module = mods.lexer },
        .{ .name = "parser", .module = mods.parser },
        .{ .name = "smt_writer", .module = mods.smt_writer },
        // test-only:
        .{ .name = "builder", .module = mods.builder },
        .{ .name = "constraint", .module = mods.constraint },
    });
    const uvl2smt_exe = b.addExecutable(.{ .name = "uvl2smt", .root_module = uvl2smt_mod });
    b.installArtifact(uvl2smt_exe);

    const any2uvl_mod = newModule(b, "src/any2uvl.zig", target, optimize, false, &.{
        .{ .name = "term", .module = mods.term },
        .{ .name = "recovery", .module = mods.recovery },
        .{ .name = "smt_reader", .module = mods.smt_reader },
        // test-only:
        .{ .name = "lexer", .module = mods.lexer },
    });
    const any2uvl_exe = b.addExecutable(.{ .name = "any2uvl", .root_module = any2uvl_mod });
    b.installArtifact(any2uvl_exe);

    const capi_mod = newModule(b, "src/capi.zig", target, optimize, false, &.{
        .{ .name = "lexer", .module = mods.lexer },
        .{ .name = "parser", .module = mods.parser },
        .{ .name = "builder", .module = mods.builder },
        .{ .name = "cnf", .module = mods.cnf },
        .{ .name = "constraint", .module = mods.constraint },
        .{ .name = "subsumption", .module = mods.subsumption },
        .{ .name = "recovery", .module = mods.recovery },
        .{ .name = "pipeline", .module = mods.pipeline },
        .{ .name = "smt_writer", .module = mods.smt_writer },
        .{ .name = "conversion", .module = mods.conversion },
    });
    const lib = b.addLibrary(.{
        .name = "uvlparser",
        .linkage = .dynamic,
        .root_module = capi_mod,
    });
    b.installArtifact(lib);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run uvl2cnf");
    run_step.dependOn(&run_cmd.step);

    // Tests always run Debug (safety checks on), independent of the
    // exe/lib's own optimize mode -- a second copy of the module graph,
    // since a Module is tied to one optimize mode for its lifetime.
    const test_step = b.step("test", "Run unit tests");
    const test_mods = buildModules(b, target, .Debug, false);
    const test_modules = [_]*std.Build.Module{
        test_mods.lexer,
        test_mods.builder,
        test_mods.parser,
        test_mods.constraint,
        test_mods.cnf,
        test_mods.subsumption,
        test_mods.conversion,
        test_mods.smt_writer,
        test_mods.smt_reader,
        test_mods.recovery,
        test_mods.pipeline,
    };
    for (test_modules) |m| {
        const t = b.addTest(.{ .root_module = m });
        const run_t = b.addRunArtifact(t);
        test_step.dependOn(&run_t.step);
    }

    // any2uvl.zig is the only CLI entry point with real tests of its own
    // (sniffFormat, verifyRecovery) -- uvl2cnf/uvl2uvl/uvl2smt have none,
    // their dependencies are already covered by test_modules above.
    const any2uvl_test_mod = newModule(b, "src/any2uvl.zig", target, .Debug, false, &.{
        .{ .name = "term", .module = test_mods.term },
        .{ .name = "recovery", .module = test_mods.recovery },
        .{ .name = "smt_reader", .module = test_mods.smt_reader },
    });
    const any2uvl_test = b.addTest(.{ .root_module = any2uvl_test_mod });
    test_step.dependOn(&b.addRunArtifact(any2uvl_test).step);
}

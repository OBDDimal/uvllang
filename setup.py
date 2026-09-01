"""
Custom build hook for the Zig backend.

Static metadata (name, dependencies, ...) all stays in pyproject.toml;
this file exists only to compile parser/ (the Zig
uvl2cnf/uvl2uvl/uvl2smt/any2uvl binaries + libuvlparser shared library) during `pip
install`/`build`, the same way python-sat's own setup.py compiles its
bundled SAT solvers before the standard build runs (a custom `build`
command subclass, hooked in via `cmdclass`, that does the native compile
step and then calls the normal build) -- so uvl2cnf/uvl2uvl/uvl2smt/any2uvl end up on PATH
as real installed scripts without a separate manual `zig build` step.
"""

import glob
import os
import platform
import shutil
import subprocess

from setuptools import setup
from setuptools.command.build import build as _build
from setuptools.dist import Distribution

# Public alias for setuptools' vendored distutils fork, same as python-sat's
# own setup.py importing `distutils.command.build`/`build_ext` -- works
# because `setuptools` (imported above) installs an import hook redirecting
# `distutils` here.
import distutils.command.build_scripts

PARSER_DIR = "parser"
_EXE_SUFFIX = ".exe" if platform.system() == "Windows" else ""
# setuptools requires scripts= paths relative to setup.py's own directory
# (this file), which is also PARSER_DIR's parent, so this is unambiguous
# regardless of the caller's cwd.
ZIG_BINS = [
    os.path.join(PARSER_DIR, "zig-out", "bin", name + _EXE_SUFFIX)
    for name in ("uvl2cnf", "uvl2uvl", "uvl2smt", "any2uvl")
]

# Where uvllang/_zig.py looks first for the compiled shared library inside
# an installed (non-editable) package -- see its own module docstring.
# build_zig() copies zig-out's .so/.dylib/.dll here so package_data (see
# pyproject.toml) actually bundles it into the wheel; without a real file
# here at build time, package_data has nothing to collect.
_LIB_BUNDLE_DIR = os.path.join("uvllang", "_zig_libs")

# Set to "1" by pyodide-build inside its build environment (the standard
# signal recommended by the Pyodide packaging docs for a setup.py to
# distinguish a `pyodide build` invocation from a normal native one).
_PYODIDE = os.environ.get("PYODIDE") == "1"


def _emscripten_sysroot():
    """Locates emscripten's sysroot via em-config, needed by `zig build`'s
    `--sysroot` for the wasm32-emscripten target.
    """
    if shutil.which("em-config") is None:
        raise RuntimeError(
            "PYODIDE=1 but emscripten (em-config) is not on PATH -- "
            "pyodide-build's environment should provide it."
        )
    cache = subprocess.run(
        ["em-config", "CACHE"], check=True, capture_output=True, text=True
    ).stdout.strip()
    return os.path.join(cache, "sysroot")


def _bundle_lib():
    """Copies zig-out/lib's one shared library into _LIB_BUNDLE_DIR, so
    package_data has a real file to collect into the wheel. Clears any
    previous contents first -- a stale library from a prior build (e.g.
    native leftovers before a Pyodide build) must not get bundled instead
    of the one this invocation actually produced.
    """
    shutil.rmtree(_LIB_BUNDLE_DIR, ignore_errors=True)
    os.makedirs(_LIB_BUNDLE_DIR, exist_ok=True)
    libs = glob.glob(os.path.join(PARSER_DIR, "zig-out", "lib", "libuvlparser.*"))
    if not libs:
        raise RuntimeError(
            f"`zig build` did not produce a shared library in {PARSER_DIR}/zig-out/lib"
        )
    for lib in libs:
        shutil.copy2(lib, _LIB_BUNDLE_DIR)


def build_zig():
    if shutil.which("zig") is None:
        raise RuntimeError(
            "The Zig toolchain is required to build uvllang (it compiles "
            "the uvl2cnf/uvl2uvl/uvl2smt/any2uvl binaries and the shared library the "
            "Python API's default backend uses). Install it from "
            "https://ziglang.org/download/ and retry."
        )
    if _PYODIDE:
        # Only libuvlparser.so applies under Pyodide -- the 4 CLI binaries
        # have no meaningful subprocess model in a browser, and Zig's std
        # start code has no wasm32-emscripten entry point to build them
        # against at all (see parser/build.zig's `pyodide` option).
        subprocess.run(
            [
                "zig", "build", "-Dpyodide=true",
                "--sysroot", _emscripten_sysroot(),
                "-Doptimize=ReleaseSmall",
            ],
            cwd=PARSER_DIR,
            check=True,
        )
        wasm_lib = os.path.join(PARSER_DIR, "zig-out", "lib", "libuvlparser.so")
        if not os.path.exists(wasm_lib):
            raise RuntimeError(f"`zig build -Dpyodide=true` did not produce {wasm_lib}")
        _bundle_lib()
        return
    subprocess.run(["zig", "build"], cwd=PARSER_DIR, check=True)
    for zig_bin in ZIG_BINS:
        if not os.path.exists(zig_bin):
            raise RuntimeError(f"`zig build` did not produce {zig_bin}")
    _bundle_lib()


# Legacy backends (uvllang.antlr4/uvllang.lark) are dead weight in a
# Pyodide build: backend="zig" is the only one that matters there, and
# neither is imported at module load time (UVL._backend_module() only
# imports one on first actual use of that backend, so dropping the
# package files themselves changes no documented behavior -- a caller
# that explicitly requests backend="lark"/"antlr" gets the same clean
# ImportError as if the optional dependency were simply never installed).
_LEGACY_BACKEND_PACKAGES = ("antlr4", "lark")


def _exclude_legacy_backends(build_lib):
    for pkg in _LEGACY_BACKEND_PACKAGES:
        shutil.rmtree(os.path.join(build_lib, "uvllang", pkg), ignore_errors=True)


class build(_build):
    """Compiles parser/ before the standard build runs, so `scripts=`
    below finds real uvl2cnf/uvl2uvl/uvl2smt/any2uvl binaries to install by the time
    they're needed, and package_data (pyproject.toml) finds a real shared
    library under uvllang/_zig_libs/ (build_zig() -> _bundle_lib()) to
    include in the wheel. Under Pyodide (PYODIDE=1), no scripts are
    installed -- only the shared library applies there -- and the legacy
    backend packages are dropped post-build (_exclude_legacy_backends()).
    """

    def run(self):
        build_zig()
        super().run()
        if _PYODIDE:
            _exclude_legacy_backends(self.build_lib)


class BinaryDistribution(Distribution):
    """Tells setuptools/wheel this distribution isn't pure Python, despite
    having no ext_modules -- the compiled shared library only ever reaches
    Python via ctypes, not the extension-module mechanism setuptools
    checks by default, so without this override bdist_wheel would tag the
    wheel `py3-none-any` and every platform would silently get the same
    (single-platform) prebuilt library.
    """

    def has_ext_modules(self):
        return True


try:
    from wheel.bdist_wheel import bdist_wheel as _bdist_wheel

    class bdist_wheel(_bdist_wheel):
        """Forces the `py3-none-<platform>` tag instead of a
        CPython-version-specific one (e.g. `cp312-cp312-<platform>`):
        ctypes has no Python-version-specific ABI, so one wheel per
        platform covers every CPython 3.x, not one per minor version.
        """

        def get_tag(self):
            _, _, plat = super().get_tag()
            return "py3", "none", plat

except ImportError:
    bdist_wheel = None


class build_scripts(distutils.command.build_scripts.build_scripts):
    """The base copy_scripts() assumes every entry in scripts= is a text
    script, and shebang-patches it by tokenize.open()-ing it looking for a
    `#!` line -- which raises on our compiled uvl2cnf/uvl2uvl/uvl2smt/any2uvl binaries
    (arbitrary bytes, not text). They need no shebang: they're already
    native executables, so just copy + chmod them verbatim instead.
    """

    def copy_scripts(self):
        self.mkpath(self.build_dir)
        outfiles = []
        for script in self.scripts:
            dest = os.path.join(self.build_dir, os.path.basename(script))
            self.copy_file(script, dest)
            outfiles.append(dest)
            if not self.dry_run:
                os.chmod(dest, 0o755)
        return outfiles, []


_cmdclass = {"build": build, "build_scripts": build_scripts}
if bdist_wheel is not None:
    _cmdclass["bdist_wheel"] = bdist_wheel

setup(
    distclass=BinaryDistribution,
    cmdclass=_cmdclass,
    scripts=[] if _PYODIDE else ZIG_BINS,
)

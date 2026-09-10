"""
Build + smoke-test for the Pyodide/wasm32-emscripten build of
libuvlparser.so (see README.md#pyodide--webassembly).

Builds into an isolated `--prefix` directory rather than parser/zig-out
so it never clobbers the native artifacts test_zig_parser.py and the rest
of the suite depend on (a wasm32-emscripten libuvlparser.so at that path
would make every other test's ctypes.CDLL load fail or misbehave).

The smoke test itself instantiates the built module directly in Node
(pyodide_smoke.mjs), with no Emscripten/Pyodide runtime involved --
Pyodide isn't installable/runnable in a plain pytest environment. This
proves the module is a functionally correct wasm dynamic-linking side
module (real parse + CNF generation, not just "compiles"); it does not
exercise Pyodide's own dynamic linker or ctypes shim.
"""

import glob
import json
import os
import shutil
import subprocess
import tempfile

import pytest
from pysat.formula import CNF

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARSER_DIR = os.path.join(ROOT, "parser")
SMOKE_SCRIPT = os.path.join(ROOT, "tests", "pyodide_smoke.mjs")

_SIMPLE_UVL = "features\n\tRoot\n\t\tmandatory\n\t\t\tA\n"


def _emscripten_sysroot():
    """Locates Emscripten via pyodide-build's own xbuildenv, the same way
    `pyodide build` (and setup.py's PYODIDE=1 path, run from inside that
    build) find it -- pyodide-build manages a private, correctly-pinned
    Emscripten under ~/.cache/pyodide-build/... (installed via `pyodide
    xbuildenv install-emscripten`), entirely independent of the outer
    shell's PATH. A bare `shutil.which("em-config")` finds nothing here
    (it's never put on PATH outside of a `pyodide build` subprocess) even
    when Emscripten is fully installed and working -- see README.md
    #pyodide--webassembly.
    """
    if shutil.which("pyodide") is None:
        return None
    emscripten_dir = subprocess.run(
        ["pyodide", "config", "get", "emscripten_dir"],
        capture_output=True,
        text=True,
    ).stdout.strip()
    em_config = os.path.join(emscripten_dir, "em-config")
    if not emscripten_dir or not os.path.exists(em_config):
        return None
    cache = subprocess.run(
        [em_config, "CACHE"], check=True, capture_output=True, text=True
    ).stdout.strip()
    return os.path.join(cache, "sysroot")


@pytest.fixture(scope="session")
def pyodide_lib(tmp_path_factory):
    """Builds libuvlparser.so for wasm32-emscripten into an isolated
    --prefix directory, torn down at the end of the session. Skips if
    zig, emscripten, or node aren't available.
    """
    if shutil.which("zig") is None:
        pytest.skip("zig toolchain not available")
    if shutil.which("node") is None:
        pytest.skip("node not available (needed to run the wasm smoke test)")
    sysroot = _emscripten_sysroot()
    if sysroot is None:
        pytest.skip("emscripten (em-config) not available")

    prefix = tmp_path_factory.mktemp("pyodide-build")
    subprocess.run(
        [
            "zig", "build", "-Dpyodide=true",
            "--sysroot", sysroot,
            "-Doptimize=ReleaseSmall",
            "--prefix", str(prefix),
        ],
        cwd=PARSER_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    lib_path = prefix / "lib" / "libuvlparser.so"
    assert lib_path.exists(), (
        f"`zig build -Dpyodide=true` did not produce {lib_path}"
    )
    return str(lib_path)


def _run_smoke(lib_path, source):
    result = subprocess.run(
        ["node", SMOKE_SCRIPT, lib_path],
        input=source,
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (
        f"pyodide_smoke.mjs crashed:\nstdout={result.stdout}\nstderr={result.stderr}"
    )
    return json.loads(result.stdout.strip().splitlines()[-1])


def test_wasm_lib_produces_valid_module(pyodide_lib):
    with open(pyodide_lib, "rb") as f:
        magic = f.read(4)
    assert magic == b"\x00asm", "libuvlparser.so is not a wasm binary"


def test_wasm_lib_only_imports_linking_primitives(pyodide_lib):
    """A side module with no unresolved libc/Emscripten-runtime imports
    beyond the standard relocatable-module primitives is what makes the
    bare-Node instantiation (and the equivalent Pyodide dlopen) work
    without a full Emscripten JS runtime.
    """
    script = f"""
import fs from "fs";
const buf = fs.readFileSync({pyodide_lib!r});
const mod = await WebAssembly.compile(buf);
console.log(JSON.stringify(WebAssembly.Module.imports(mod).map(i => i.name)));
"""
    result = subprocess.run(
        ["node", "--input-type=module"], input=script,
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr
    names = set(json.loads(result.stdout.strip().splitlines()[-1]))
    assert names == {
        "memory", "__indirect_function_table",
        "__stack_pointer", "__memory_base", "__table_base",
    }


def test_wasm_source_to_cnf_smoke(pyodide_lib):
    out = _run_smoke(pyodide_lib, _SIMPLE_UVL)
    assert out["rc"] == 0, out.get("error")
    cnf = CNF(from_string=out["dimacs"])
    id_to_name = {
        int(parts[1]): parts[2]
        for parts in (c.strip().split(None, 2) for c in cnf.comments)
        if len(parts) >= 3
    }
    assert set(id_to_name.values()) == {"Root", "A"}
    # Root is asserted true, and A mandatory-child of Root: Root, A <-> Root,
    # encoded as (Root)∧(¬A∨Root)∧(¬Root∨A).
    root_id = next(i for i, n in id_to_name.items() if n == "Root")
    a_id = next(i for i, n in id_to_name.items() if n == "A")
    lits = {frozenset(c) for c in cnf.clauses}
    assert lits == {
        frozenset([root_id]),
        frozenset([-a_id, root_id]),
        frozenset([-root_id, a_id]),
    }


@pytest.mark.parametrize(
    "uvl_file",
    sorted(glob.glob(os.path.join(ROOT, "examples", "*.uvl"))),
)
def test_wasm_source_to_cnf_examples_do_not_crash(pyodide_lib, uvl_file):
    """Every real example model at least runs through the wasm build's
    pipeline without crashing/trapping -- not a correctness check (that's
    covered natively in test_zig_parser.py), just breadth-of-input
    robustness for this target specifically.
    """
    with open(uvl_file) as f:
        source = f.read()
    out = _run_smoke(pyodide_lib, source)
    assert "rc" in out, out

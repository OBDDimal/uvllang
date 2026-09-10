"""
Tests for the native `uvl2smt` binary (parser/src/smt/writer.zig / uvl2smt.zig),
using z3 as an external correctness oracle: an emitted .smt2 file must at
minimum parse and solve without error under z3, and satisfiability must
match what we can independently confirm.

Mirrors tests/test_zig_parser.py's pattern (session-scoped fixture builds
the binary once, subprocess invokes it) rather than tests/test_arithmetic.py's
Python-API-level tests, since uvl2smt is a pure native binary with no
Python involved.
"""

import glob
import os
import shutil
import subprocess

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARSER_DIR = os.path.join(ROOT, "parser")
ZIG_BIN = os.path.join(PARSER_DIR, "zig-out", "bin", "uvl2smt")
EXAMPLES = os.path.join(ROOT, "examples")

EXAMPLE_UVL_FILES = sorted(glob.glob(os.path.join(EXAMPLES, "*.uvl")))


@pytest.fixture(scope="session")
def uvl2smt_bin():
    if shutil.which("zig") is None:
        pytest.skip("zig toolchain not available")
    subprocess.run(
        ["zig", "build"], cwd=PARSER_DIR, check=True, capture_output=True, text=True
    )
    assert os.path.exists(ZIG_BIN), "uvl2smt binary was not produced by `zig build`"
    return ZIG_BIN


@pytest.fixture(scope="session")
def z3_bin():
    path = shutil.which("z3") or os.path.join(ROOT, ".venv", "bin", "z3")
    if not os.path.exists(path) and shutil.which(path) is None:
        pytest.skip("z3 CLI not available")
    return path


def _run_uvl2smt(uvl2smt_bin, uvl_path, out_path):
    result = subprocess.run(
        [uvl2smt_bin, uvl_path, out_path], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stderr
    assert os.path.exists(out_path)


@pytest.mark.parametrize(
    "uvl_path", EXAMPLE_UVL_FILES, ids=[os.path.basename(p) for p in EXAMPLE_UVL_FILES]
)
def test_smt_output_is_accepted_by_z3(uvl2smt_bin, z3_bin, uvl_path, tmp_path):
    """Every example model's emitted .smt2 must parse and solve under z3
    with no error, and must be satisfiable (every example is a real,
    configurable feature model -- none is a deliberately-contradictory
    fixture)."""
    out_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(uvl2smt_bin, uvl_path, out_path)

    result = subprocess.run(
        [z3_bin, "-T:30", out_path], capture_output=True, text=True, timeout=60
    )
    for line in result.stdout.splitlines():
        assert not line.strip().startswith("(error"), result.stdout
    assert result.stdout.strip().startswith("sat"), (
        f"expected sat, got: {result.stdout!r} stderr: {result.stderr!r}"
    )


def test_smt_output_matches_python_bindings(uvl2smt_bin, tmp_path):
    z3 = pytest.importorskip("z3")
    out_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(
        uvl2smt_bin, os.path.join(EXAMPLES, "berkeleydb.uvl"), out_path
    )
    with open(out_path) as f:
        smt_text = f.read()

    solver = z3.Solver()
    solver.from_string(smt_text)
    assert str(solver.check()) == "sat"


def test_quoted_feature_names_round_trip_through_z3(uvl2smt_bin, tmp_path):
    """A UVL-quoted feature name must become a valid SMT-LIB symbol (bare
    or |...|-quoted), not be emitted with its source quote characters
    intact."""
    z3 = pytest.importorskip("z3")
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text(
        'features\n    "My Root"\n        optional\n            A\n'
    )
    out_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(uvl2smt_bin, str(uvl_path), out_path)
    with open(out_path) as f:
        smt_text = f.read()

    assert '"My Root"' not in smt_text
    assert "|My Root|" in smt_text
    solver = z3.Solver()
    solver.from_string(smt_text)
    assert str(solver.check()) == "sat"


def test_string_valued_attribute_declared_as_string_sort(uvl2smt_bin, tmp_path):
    """A string-valued attribute must be declared (and asserted) as
    SMT-LIB String, not Int."""
    z3 = pytest.importorskip("z3")
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text(
        "features\n    Root {tag 'v1'}\n        optional\n            A\n"
    )
    out_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(uvl2smt_bin, str(uvl_path), out_path)
    with open(out_path) as f:
        smt_text = f.read()

    assert "(declare-const Root.tag String)" in smt_text
    solver = z3.Solver()
    solver.from_string(smt_text)
    assert str(solver.check()) == "sat"


def test_help_flag(uvl2smt_bin):
    result = subprocess.run([uvl2smt_bin, "--help"], capture_output=True, text=True)
    assert result.returncode == 0
    # Zig's std.debug.print goes to stderr, not stdout.
    assert "uvl2smt" in result.stdout + result.stderr


def test_default_output_path(uvl2smt_bin, tmp_path):
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text("features\n    Root\n")
    result = subprocess.run(
        [uvl2smt_bin, str(uvl_path)], capture_output=True, text=True, cwd=tmp_path
    )
    assert result.returncode == 0, result.stderr
    assert (tmp_path / "model.smt2").exists()


# ---------------------------------------------------------------------------
# any2uvl's .smt2 input support (parser/src/smt/reader.zig, parser/src/any2uvl.zig)
# ---------------------------------------------------------------------------

ANY2UVL_BIN = os.path.join(PARSER_DIR, "zig-out", "bin", "any2uvl")


@pytest.fixture(scope="session")
def any2uvl_bin():
    if shutil.which("zig") is None:
        pytest.skip("zig toolchain not available")
    subprocess.run(
        ["zig", "build"], cwd=PARSER_DIR, check=True, capture_output=True, text=True
    )
    assert os.path.exists(ANY2UVL_BIN), "any2uvl binary was not produced by `zig build`"
    return ANY2UVL_BIN


def _norm(name):
    return name.strip().strip('"').strip("'").strip()


def test_any2uvl_detects_smt2_by_content_not_extension(
    uvl2smt_bin, any2uvl_bin, tmp_path
):
    """Format is sniffed from content (leading `;` comments skipped), not
    the file extension -- feed it a .smt2 file under a misleading name."""
    uvl_path = os.path.join(EXAMPLES, "eshop.uvl")
    smt_path = str(tmp_path / "model.weirdext")
    _run_uvl2smt(uvl2smt_bin, uvl_path, smt_path)

    out_path = str(tmp_path / "recovered.uvl")
    result = subprocess.run(
        [any2uvl_bin, smt_path, out_path], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stderr
    assert os.path.exists(out_path)


def test_any2uvl_smt2_round_trip_is_logically_equivalent(
    uvl2smt_bin, any2uvl_bin, tmp_path
):
    """uvl2smt -> any2uvl --optimize --byname must recover a UVL model
    logically equivalent to the original, exactly like the existing
    DIMACS round trip in tests/test_recovery_quality.py."""
    from uvllang import UVL
    from pysat.solvers import Glucose3

    uvl_path = os.path.join(EXAMPLES, "berkeleydb.uvl")
    smt_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(uvl2smt_bin, uvl_path, smt_path)

    out_path = str(tmp_path / "recovered.uvl")
    result = subprocess.run(
        [any2uvl_bin, smt_path, out_path, "--optimize", "--byname"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr

    orig = UVL(from_file=uvl_path, backend="zig")
    recovered = UVL(from_file=out_path, backend="zig")

    orig_feats = sorted(set(_norm(f) for f in orig.features))
    rec_feats = sorted(set(_norm(f) for f in recovered.features))
    assert orig_feats == rec_feats

    # orig_cnf/rec_cnf each assign their own ids; compare by normalized
    # name (quoting can differ between the original and recovered UVL),
    # renumbered here onto one shared, freshly assigned id space (see
    # tests/test_recovery_quality.py's _dimacs_equivalent).
    orig_cnf = orig.to_cnf()
    rec_cnf = recovered.to_cnf()
    orig_id_to_name = {
        int(ident): _norm(name)
        for _, ident, name in (c.split(" ", 2) for c in orig_cnf.comments)
    }
    rec_id_to_name = {
        int(ident): _norm(name)
        for _, ident, name in (c.split(" ", 2) for c in rec_cnf.comments)
    }

    names = sorted(set(orig_id_to_name.values()) | set(rec_id_to_name.values()))
    ids = {name: i + 1 for i, name in enumerate(names)}

    def _renumbered(clauses, id_to_name):
        return frozenset(
            tuple(
                sorted(
                    ids[id_to_name[lit]] if lit > 0 else -ids[id_to_name[-lit]]
                    for lit in clause
                )
            )
            for clause in clauses
        )

    o = _renumbered(orig_cnf.clauses, orig_id_to_name)
    r = _renumbered(rec_cnf.clauses, rec_id_to_name)
    missing = o - r
    extra = r - o

    def entailed(solver, clause):
        return not solver.solve(assumptions=[-l for l in clause])

    if missing:
        with Glucose3(bootstrap_with=[list(c) for c in r]) as s:
            assert all(entailed(s, c) for c in missing)
    if extra:
        with Glucose3(bootstrap_with=[list(c) for c in o]) as s:
            assert all(entailed(s, c) for c in extra)


def test_any2uvl_preserves_arithmetic_constraints_as_residual_text(
    uvl2smt_bin, any2uvl_bin, tmp_path
):
    """A non-Boolean assert (attribute value binding, arithmetic
    constraint) must survive the SMT-LIB round trip as a residual UVL
    constraint, not be silently dropped."""
    uvl_path = os.path.join(EXAMPLES, "expressions.uvl")
    smt_path = str(tmp_path / "model.smt2")
    _run_uvl2smt(uvl2smt_bin, uvl_path, smt_path)

    out_path = str(tmp_path / "recovered.uvl")
    result = subprocess.run(
        [any2uvl_bin, smt_path, out_path], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stderr

    with open(out_path) as f:
        recovered_text = f.read()
    assert "constraints" in recovered_text
    # At least one attribute-value-binding assert must have round-tripped.
    assert ".Price" in recovered_text or ".Fun" in recovered_text


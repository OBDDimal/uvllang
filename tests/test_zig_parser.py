"""
Equivalence tests for the Zig UVL parser (parser/uvlparse) against the
Python (Lark) implementation's to_cnf().

Compares actual DIMACS output between both implementations on every real
example model plus synthetic snippets covering grammar corners the real
examples don't exercise. A clause-set mismatch means the two parsers
disagree about what the feature model means.
"""

import glob
import os
import shutil
import subprocess

import pytest

from uvllang import UVL, _zig

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARSER_DIR = os.path.join(ROOT, "parser")
ZIG_BIN = os.path.join(PARSER_DIR, "zig-out", "bin", "uvlparse")


@pytest.fixture(scope="session")
def zig_parser():
    """Builds parser/ and returns the path to the uvlparse binary. Skips
    dependent tests if the zig toolchain isn't available.
    """
    if shutil.which("zig") is None:
        pytest.skip("zig toolchain not available")
    subprocess.run(
        ["zig", "build", "-Doptimize=ReleaseSafe"],
        cwd=PARSER_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    assert os.path.exists(ZIG_BIN), "uvlparse binary was not produced by `zig build`"
    return ZIG_BIN


def _read_dimacs(path):
    """Clauses as a set of frozensets (order- and duplicate-insensitive,
    matching DIMACS clause semantics) plus the id-to-name comment mapping.
    """
    clauses = set()
    comments = {}
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("c "):
                _, ident, name = line.split(" ", 2)
                comments[int(ident)] = name
            elif line.startswith("p ") or not line.strip():
                continue
            else:
                lits = [int(x) for x in line.split() if x != "0"]
                clauses.add(frozenset(lits))
    return clauses, comments


def _run_zig(zig_parser, uvl_path, out_path):
    result = subprocess.run(
        [zig_parser, uvl_path, out_path], capture_output=True, text=True
    )
    assert result.returncode == 0, (
        f"uvlparse failed on {uvl_path}:\nstdout: {result.stdout}\nstderr: {result.stderr}"
    )


def _python_dimacs(uvl_path, out_path):
    model = UVL(from_file=uvl_path)
    features2ids = {f: i + 1 for i, f in enumerate(sorted(set(model.features)))}
    model.to_cnf(features2ids, verbose_info=False).to_file(out_path)


def _assert_equivalent(zig_out, py_out):
    zig_clauses, zig_comments = _read_dimacs(str(zig_out))
    py_clauses, py_comments = _read_dimacs(str(py_out))

    assert zig_comments == py_comments, "feature id<->name mapping differs"
    only_zig = zig_clauses - py_clauses
    only_py = py_clauses - zig_clauses
    assert not only_zig and not only_py, (
        f"clause sets differ: {len(only_zig)} zig-only, {len(only_py)} py-only\n"
        f"zig-only sample: {list(only_zig)[:3]}\n"
        f"py-only sample: {list(only_py)[:3]}"
    )


EXAMPLE_UVL_FILES = sorted(glob.glob(os.path.join(ROOT, "examples", "*.uvl")))


@pytest.mark.parametrize(
    "uvl_path",
    EXAMPLE_UVL_FILES,
    ids=[os.path.basename(p) for p in EXAMPLE_UVL_FILES],
)
def test_zig_matches_python_on_examples(zig_parser, uvl_path, tmp_path):
    zig_out = tmp_path / "zig.dimacs"
    py_out = tmp_path / "py.dimacs"
    _run_zig(zig_parser, uvl_path, str(zig_out))
    _python_dimacs(uvl_path, str(py_out))
    _assert_equivalent(zig_out, py_out)


# Grammar corners none of the real example models happen to exercise.
SYNTHETIC_SNIPPETS = {
    "block_and_line_comments": """\
/* a block comment
   spanning multiple lines */
namespace Test // trailing line comment

features
    Root
        mandatory
            A
        optional
            B
""",
    "includes_and_imports": """\
namespace Test

include
    Boolean
    Arithmetic.group-cardinality

imports
    some.other.model as som

features
    Root
        optional
            A
""",
    "negative_and_float_attributes": """\
features
    Root {weight -3, ratio -2.5}
        optional
            A {weight 1.25}

constraints
    Root => A
""",
    "quoted_feature_names_as_literals": """\
features
    "Root Feature"
        optional
            "Child A"
            "Child B"

constraints
    "Child A" => "Root Feature"
    "Child A" | "Child B"
""",
    "single_quoted_strings_and_deep_nesting": """\
features
    Root
        optional
            A
            B
            C

constraints
    ((A | B) & (!C | A)) => (Root & !(B & C))
    B <=> (A & !C)
""",
    "cardinality_group_with_cross_tree_constraint": """\
features
    Root cardinality [1..3]
        alternative
            A
            B
            C
        or
            D
            E

constraints
    A => D
    B <=> E
""",
    "boolean_and_typed_feature_values": """\
features
    Root
        optional
            String Label {default 'hello'}
            Boolean Flag {enabled true}
            Integer Count {value 0}

constraints
    Flag => Label
""",
}


@pytest.mark.parametrize("name", sorted(SYNTHETIC_SNIPPETS.keys()))
def test_zig_matches_python_on_synthetic_snippets(zig_parser, name, tmp_path):
    uvl_path = tmp_path / f"{name}.uvl"
    uvl_path.write_text(SYNTHETIC_SNIPPETS[name])

    zig_out = tmp_path / "zig.dimacs"
    py_out = tmp_path / "py.dimacs"
    _run_zig(zig_parser, str(uvl_path), str(zig_out))
    _python_dimacs(str(uvl_path), str(py_out))
    _assert_equivalent(zig_out, py_out)


# uvllang._zig.parse_source_to_cnf (full pipeline) vs. hierarchy_to_cnf
# (hybrid mode, fed by an already-parsed hierarchy) compared directly
# against each other: a mismatch means the ctypes marshalling disagrees
# with Zig's own native parse.


def _named_clauses(clauses, id_to_name):
    return {
        frozenset(
            id_to_name[lit] if lit > 0 else f"!{id_to_name[-lit]}" for lit in clause
        )
        for clause in clauses
    }


@pytest.mark.parametrize("name", sorted(SYNTHETIC_SNIPPETS.keys()))
def test_zig_capi_hierarchy_matches_full_pipeline(zig_parser, name):
    text = SYNTHETIC_SNIPPETS[name]

    full_clauses, full_id_to_name = _zig.parse_source_to_cnf(text)

    model = UVL(from_str=text)
    builder = model.builder()
    features = sorted(set(model.features))
    hybrid_clauses, hybrid_id_to_name = _zig.hierarchy_to_cnf(
        features, builder.root_feature, builder.feature_hierarchy, model.boolean_constraints
    )

    assert _named_clauses(full_clauses, full_id_to_name) == _named_clauses(
        hybrid_clauses, hybrid_id_to_name
    )

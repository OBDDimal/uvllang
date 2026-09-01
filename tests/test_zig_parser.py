"""
Equivalence tests for the Zig UVL parser (parser/uvl2cnf) against the
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
from pysat.formula import CNF

from uvllang import UVL, _zig

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PARSER_DIR = os.path.join(ROOT, "parser")
ZIG_BIN = os.path.join(PARSER_DIR, "zig-out", "bin", "uvl2cnf")


@pytest.fixture(scope="session")
def zig_parser():
    """Builds parser/ and returns the path to the uvl2cnf binary. Skips
    dependent tests if the zig toolchain isn't available.

    Deliberately doesn't pass -Doptimize: this binary is also the one
    symlinked onto PATH as the real `uvl2cnf` command (see
    uvllang/cli.py's module docstring), so overriding its optimize mode
    here would silently leave that command in whatever mode this fixture
    last used, every time the test suite runs. `zig build`'s own default
    (ReleaseFast, set in build.zig) is what should ship either way.
    """
    if shutil.which("zig") is None:
        pytest.skip("zig toolchain not available")
    subprocess.run(
        ["zig", "build"],
        cwd=PARSER_DIR,
        check=True,
        capture_output=True,
        text=True,
    )
    assert os.path.exists(ZIG_BIN), "uvl2cnf binary was not produced by `zig build`"
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
    # --simplify: the Python side (_python_dimacs below) always goes through
    # capi.zig's sourceToCnfImpl/UVL.to_cnf, which always runs the global
    # subsumption pass unconditionally. The CLI only runs it when asked
    # (see docs/pipeline_clause_dedup.md), so it must be requested here too
    # for the two sides' clause sets to be exactly comparable.
    result = subprocess.run(
        [zig_parser, uvl_path, out_path, "--simplify"], capture_output=True, text=True
    )
    assert (
        result.returncode == 0
    ), f"uvl2cnf failed on {uvl_path}:\nstdout: {result.stdout}\nstderr: {result.stderr}"


def _python_dimacs(uvl_path, out_path):
    # backend="lark": this compares the zig CLI's own native parse against
    # Lark-parsed hierarchy/constraints handed to Zig's CNF generation --
    # backend="zig" here would make it a vacuous zig-vs-zig comparison.
    # drop_non_boolean=True: some example/synthetic files exercise
    # cardinality/arithmetic constructs on purpose, to check the CNF these
    # backends produce still matches the native binary's -- that's a CNF
    # equivalence check, not the NonBooleanConstructError policy.
    # simplify=True: matches _run_zig's --simplify, so both sides run the
    # same global subsumption pass -- both default to off now (CLI and API
    # behavior intentionally match, see docs/pipeline_clause_dedup.md), so
    # without this the two sides would compare unsimplified against
    # simplified and always mismatch.
    model = UVL(
        from_file=uvl_path, backend="lark", drop_non_boolean=True, simplify=True
    )
    model.to_cnf(verbose_info=False).to_file(out_path)


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


def _named_clauses(raw_dimacs):
    """Named (not numeric) clause set, from zig's own raw DIMACS bytes --
    comparing by feature name instead of by id sidesteps the two calls
    below having no reason to agree on numbering (each assigns ids over
    its own, potentially differently-ordered, feature list)."""
    cnf = CNF(from_string=raw_dimacs.decode("utf-8"))
    id_to_name = {
        int(ident): name for _, ident, name in (c.split(" ", 2) for c in cnf.comments)
    }
    return {
        frozenset(
            id_to_name[lit] if lit > 0 else f"!{id_to_name[-lit]}" for lit in clause
        )
        for clause in cnf.clauses
    }


@pytest.mark.parametrize("name", sorted(SYNTHETIC_SNIPPETS.keys()))
def test_zig_capi_hierarchy_matches_full_pipeline(zig_parser, name):
    text = SYNTHETIC_SNIPPETS[name]

    _, full_dimacs = _zig.parse_source_to_cnf(text)

    # drop_non_boolean=True: one snippet (cardinality_group_with_cross_tree_constraint)
    # uses feature cardinality, which would otherwise raise on construction
    # now that backend="lark" also runs the same eager check backend="zig" does.
    # This test is about CNF equivalence, not the exception policy.
    model = UVL(from_str=text, backend="lark", drop_non_boolean=True)
    builder = model.builder()
    features = sorted(set(model.features))
    _, hybrid_dimacs = _zig.hierarchy_to_cnf(
        features, builder.root_feature, builder.feature_hierarchy, model.constraints
    )

    assert _named_clauses(full_dimacs) == _named_clauses(hybrid_dimacs)


# ---------------------------------------------------------------------------
# Full Lark/ANTLR parity: backend="zig" supports everything the other two
# backends do (features, types, attributes, hierarchy, constraint
# classification, to_smt()), not just to_cnf(). Constraint text and
# attribute values are compared with whitespace stripped: Lark/ANTLR
# concatenate token text with no separator (losing the original spacing),
# while zig reconstructs the real source span (keeping it) -- an
# intentional difference confirmed with the user, not a bug.
# ---------------------------------------------------------------------------


def _nows(s):
    return "".join(s.split())


def _norm_constraints(constraints):
    return {_nows(c) for c in constraints}


def _norm_attributes(feature_attributes):
    return {
        feature: {key: _nows(value) for key, value in attrs.items()}
        for feature, attrs in feature_attributes.items()
    }


@pytest.mark.parametrize(
    "uvl_path",
    EXAMPLE_UVL_FILES,
    ids=[os.path.basename(p) for p in EXAMPLE_UVL_FILES],
)
def test_zig_matches_lark_on_extraction(uvl_path):
    # drop_non_boolean=True: this test exercises extraction parity, not the
    # NonBooleanConstructError policy -- feature-cardinality.uvl (feature
    # cardinality) and the arithmetic-constraint examples would otherwise
    # raise on construction.
    zig_model = UVL(from_file=uvl_path, backend="zig", drop_non_boolean=True)
    lark_model = UVL(from_file=uvl_path, backend="lark")

    assert sorted(zig_model.features) == sorted(lark_model.features)
    assert _norm_constraints(zig_model.boolean_constraints) == _norm_constraints(
        lark_model.boolean_constraints
    )
    assert _norm_constraints(zig_model.arithmetic_constraints) == _norm_constraints(
        lark_model.arithmetic_constraints
    )
    assert zig_model.feature_types == lark_model.feature_types
    assert zig_model.builder().root_feature == lark_model.builder().root_feature
    assert (
        zig_model.builder().feature_hierarchy == lark_model.builder().feature_hierarchy
    )

    # feature_attributes: compared against both other backends. Lark used
    # to silently drop a small number of attribute values on pathological
    # inputs (confirmed on automotive01.uvl, e.g.
    # N_104357__F_104406's featureDescription__) -- a real bug, not a
    # backend quirk: Lark's grammar had a genuine reduce/reduce ambiguity
    # (a bare reference used as a whole boolean constraint vs. as the
    # left-hand side of a comparison), and running it under Earley with
    # `ambiguity="explicit"` produced `_ambig` tree nodes that
    # uvllang.uvl's tree walker never accounted for, silently
    # mis-extracting on the rare input where the ambiguity was actually
    # exercised. Fixed at the grammar level (see grammars/uvl.lark's
    # `constraint_atom` and _load_lark_parser's docstring) rather than
    # worked around, so all three backends must now agree exactly.
    antlr_model = UVL(from_file=uvl_path, backend="antlr")
    assert _norm_attributes(zig_model.feature_attributes) == _norm_attributes(
        antlr_model.feature_attributes
    )
    assert _norm_attributes(lark_model.feature_attributes) == _norm_attributes(
        antlr_model.feature_attributes
    )


@pytest.mark.parametrize(
    "uvl_path",
    EXAMPLE_UVL_FILES,
    ids=[os.path.basename(p) for p in EXAMPLE_UVL_FILES],
)
def test_to_smt_is_identical_across_backends(uvl_path):
    """to_smt() delegates to uvllang._zig.source_to_smt (parser/src/
    smt.zig) for every backend -- all three must produce identical,
    solvable SMT-LIB (see tests/test_zig_smt.py for the writer's own
    detailed coverage).
    """
    z3 = pytest.importorskip("z3")
    zig_model = UVL(from_file=uvl_path, backend="zig", drop_non_boolean=True)
    antlr_model = UVL(from_file=uvl_path, backend="antlr")
    lark_model = UVL(from_file=uvl_path, backend="lark")

    zig_smt = zig_model.to_smt()
    assert zig_smt == antlr_model.to_smt() == lark_model.to_smt()

    solver = z3.Solver()
    solver.from_string(zig_smt)
    assert str(solver.check()) == "sat"


# ---------------------------------------------------------------------------
# uvl2cnf --strict: refuses instead of warning when a construct above the
# Boolean language level would be silently dropped (parser/src/main.zig,
# parser/src/pipeline.zig's NonBooleanCounts.isThreatening).


def test_strict_fails_on_group_cardinality(zig_parser, tmp_path):
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text(
        "features\n    Root\n        [2..3]\n            A\n            B\n            C\n"
    )
    result = subprocess.run(
        [zig_parser, "--strict", str(uvl_path), str(tmp_path / "out.dimacs")],
        capture_output=True,
        text=True,
    )
    assert result.returncode != 0
    assert "refusing" in result.stderr


def test_strict_succeeds_without_non_boolean_constructs(zig_parser, tmp_path):
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text("features\n    Root\n        mandatory\n            A\n")
    out_path = tmp_path / "out.dimacs"
    result = subprocess.run(
        [zig_parser, "--strict", str(uvl_path), str(out_path)],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert out_path.exists()


def test_strict_with_conversion_succeeds_on_group_cardinality(zig_parser, tmp_path):
    uvl_path = tmp_path / "model.uvl"
    uvl_path.write_text(
        "features\n    Root\n        [2..3]\n            A\n            B\n            C\n"
    )
    result = subprocess.run(
        [
            zig_parser,
            "--strict",
            "--conversion",
            str(uvl_path),
            str(tmp_path / "out.dimacs"),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr


def test_is_non_boolean_threatening_matches_uvl_drop_non_boolean():
    """uvllang._zig.is_non_boolean_threatening (ctypes -> capi.zig's
    NonBooleanCounts.isThreatening) is the single source of truth
    UVL(drop_non_boolean=False) relies on -- exercise it directly."""
    threatening = {
        "cardinality_groups": 1,
        "constraint_attributes": 0,
        "cardinality_features": 0,
        "attribute_ref_constraints": 0,
        "comparison_constraints": 0,
        "typed_features": 0,
        "attributed_features": 0,
    }
    assert _zig.is_non_boolean_threatening(threatening, conversion=False)
    assert not _zig.is_non_boolean_threatening(threatening, conversion=True)

    tier3_only = {**threatening, "cardinality_groups": 0, "typed_features": 1}
    assert not _zig.is_non_boolean_threatening(tier3_only, conversion=False)

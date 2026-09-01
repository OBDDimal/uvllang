"""
Tests for the UVL Parser implementation.

These tests verify that both Lark and ANTLR parsers correctly parse UVL files
and produce consistent results.
"""

import pytest
import os
from uvllang import UVL
from uvllang.uvl import NonBooleanConstructError

BACKENDS = ["zig", "lark", "antlr"]


def _cnf_satisfied(clauses, assignment):
    """assignment: dict of 1-based variable id -> bool. True if every clause
    has at least one satisfied literal under the given assignment."""
    return all(
        any((lit > 0) == assignment[abs(lit)] for lit in clause) for clause in clauses
    )


def _ids_by_name(cnf):
    """name -> id, from a CNF's own "c <id> <name>" comments (uvl2cnf's
    id assignment is deterministic but not caller-chosen, so tests read
    it back instead of asserting a fixed numbering)."""
    return {name: int(ident) for _, ident, name in (c.split(" ", 2) for c in cnf.comments)}


# Test data for all example files
EXAMPLE_FILES = [
    {
        "file": "automotive01.uvl",
        "features": 2513,
        "bool_constraints": 2833,
        "arith_constraints": 0,
        "cnf_clauses": 10311,
        "has_attributes": True,
    },
    {
        "file": "eshop.uvl",
        "features": 173,
        "bool_constraints": 0,
        "arith_constraints": 0,
        "cnf_clauses": 289,
        "has_attributes": False,
    },
    {
        "file": "expressions.uvl",
        "features": 3,
        "bool_constraints": 0,
        "arith_constraints": 24,
        "cnf_clauses": 4,
        "has_attributes": True,
    },
    {
        "file": "aggregate.uvl",
        "features": 3,
        "bool_constraints": 0,
        "arith_constraints": 2,
        "cnf_clauses": 3,
        "has_attributes": True,
        "has_aggregates": True,
    },
    {
        "file": "aggregateFunctions.uvl",
        "features": 3,
        "bool_constraints": 0,
        "arith_constraints": 2,
        "cnf_clauses": 3,
        "has_attributes": True,
        "has_aggregates": True,
    },
    {
        "file": "lengthAggregation.uvl",
        "features": 3,
        "bool_constraints": 0,
        "arith_constraints": 3,
        "cnf_clauses": 3,
        "has_types": True,
        "has_len_function": True,
    },
    {
        "file": "feature-cardinality.uvl",
        "features": 4,
        "bool_constraints": 0,
        "arith_constraints": 0,
        "cnf_clauses": 8,
        "has_cardinality": True,
    },
]


@pytest.mark.parametrize("backend", BACKENDS)
@pytest.mark.parametrize(
    "example", EXAMPLE_FILES, ids=[e["file"] for e in EXAMPLE_FILES]
)
class TestUVLParsing:
    """Parsing + CNF generation on every real example file, identically
    across all three backends."""

    def test_uvl2cnf(self, example, backend):
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        # drop_non_boolean=True: several EXAMPLE_FILES entries (expressions,
        # aggregate*, lengthAggregation, feature-cardinality) exercise
        # arithmetic constraints / feature cardinality on purpose, to check
        # the CNF still comes out right with them dropped -- this test is
        # about parsing/CNF-generation correctness, not the
        # NonBooleanConstructError policy (covered separately in
        # TestNonBooleanConstructs).
        model = UVL(from_file=example_file, backend=backend, drop_non_boolean=True)

        assert model.tree is not None, f"{example['file']} should parse successfully"
        assert (
            len(model.features) == example["features"]
        ), f"{example['file']} should have {example['features']} features"

        assert (
            len(model.boolean_constraints) == example["bool_constraints"]
        ), f"{example['file']} should have {example['bool_constraints']} boolean constraints"
        assert (
            len(model.arithmetic_constraints) == example["arith_constraints"]
        ), f"{example['file']} should have {example['arith_constraints']} arithmetic constraints"

        cnf = model.to_cnf()

        assert (
            len(cnf.clauses) == example["cnf_clauses"]
        ), f"{example['file']} should produce {example['cnf_clauses']} CNF clauses"
        assert (
            cnf.nv == example["features"]
        ), f"CNF should have {example['features']} variables"
        assert all(isinstance(clause, list) for clause in cnf.clauses)
        assert all(isinstance(lit, int) for clause in cnf.clauses for lit in clause)


# Every group kind's exact CNF encoding, alphabetical-by-name ids (all
# three backends assign ids the same way): parent=1, member(s) 2.. --
# see uvllang._zig.hierarchy_to_cnf / cnf.zig's hierarchyToCnf.
GROUP_ENCODINGS = {
    "mandatory": {
        "uvl": "features\n    ARoot\n        mandatory\n            BChild\n",
        "expected": [[1], [-2, 1], [-1, 2]],
        "excluded": [],
    },
    "optional": {
        "uvl": "features\n    ARoot\n        optional\n            BOptionalChild\n",
        "expected": [[1], [-2, 1]],
        "excluded": [],
    },
    "alternative": {
        "uvl": "features\n    ARoot\n        alternative\n            BChildA\n            CChildB\n",
        "expected": [[1], [-2, 1], [-3, 1], [-1, 2, 3], [-2, -3]],
        "excluded": [],
    },
    "or": {
        "uvl": "features\n    ARoot\n        or\n            BChildA\n            CChildB\n",
        "expected": [[1], [-2, 1], [-3, 1], [-1, 2, 3]],
        # unlike "alternative", an or-group doesn't forbid selecting both
        # children.
        "excluded": [[-2, -3]],
    },
}


@pytest.mark.parametrize("backend", BACKENDS)
@pytest.mark.parametrize("kind", GROUP_ENCODINGS.keys())
def test_group_kind_cnf_encoding(kind, backend):
    spec = GROUP_ENCODINGS[kind]
    model = UVL(from_str=spec["uvl"], backend=backend)
    cnf = model.to_cnf()
    for clause in spec["expected"]:
        assert clause in cnf.clauses, f"{kind}: missing {clause} in {cnf.clauses}"
    for clause in spec["excluded"]:
        assert clause not in cnf.clauses, f"{kind}: unexpected {clause} in {cnf.clauses}"
    assert len(cnf.clauses) == len(spec["expected"]), f"{kind}: {cnf.clauses}"


@pytest.mark.parametrize("backend", BACKENDS)
class TestUVLFeatures:
    """UVL language features not already covered by TestUVLParsing/
    GROUP_ENCODINGS: attribute/constraint extraction, error handling, and
    the equivalence-operator regressions."""

    def test_parse_simple_inline_uvl(self, backend):
        uvl_content = """namespace TestNS

features
    Root
        mandatory
            FeatureA
        optional
            FeatureB
"""
        model = UVL(from_str=uvl_content, backend=backend)
        assert model.tree is not None
        assert len(model.features) == 3
        assert "Root" in model.features
        assert "FeatureA" in model.features
        assert "FeatureB" in model.features

    def test_invalid_content_raises_error(self, backend):
        with pytest.raises(Exception):
            UVL(from_str="This is not valid UVL syntax!", backend=backend)

    def test_nonexistent_file_raises_error(self, backend):
        with pytest.raises(FileNotFoundError):
            UVL(from_file="nonexistent_file.uvl", backend=backend)

    def test_builder_external_usage_and_feature_iteration(self, backend):
        """builder() is usable from outside the class and visits every
        feature in the model."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, backend=backend)
        builder = model.builder()

        assert builder.root_feature is not None
        assert builder.feature_hierarchy is not None
        assert set(builder.feature_hierarchy.keys()) == set(model.features)
        assert len(builder.feature_hierarchy) == 173

    def test_implication_constraints_automotive01(self, backend):
        automotive_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=automotive_file, backend=backend)
        implication_constraints = [c for c in model.boolean_constraints if "=>" in c]
        assert (
            len(implication_constraints) > 0
        ), "Should have implication (=>) constraints"

    @pytest.mark.parametrize(
        "constraint_text", ["A <=> B", "A<=>B", "A <=>B", "A<=> B"]
    )
    def test_cnf_equivalence_constraint(self, backend, constraint_text):
        """Regression: <=> must not be mistaken for an arithmetic comparison.

        _constraints_to_cnf used to strip only "=>" from the constraint text
        before checking for stray comparison operators; stripping "=>" out
        of "<=>" leaves a "<" behind, which made every equivalence
        constraint get silently skipped as an "arithmetic comparison" --
        regardless of whitespace around the operator.
        """
        uvl_content = f"""features
    ARoot
        optional
            A
            B

constraints
    {constraint_text}
"""
        model = UVL(from_str=uvl_content, backend=backend)
        assert len(model.boolean_constraints) == 1
        assert len(model.arithmetic_constraints) == 0

        cnf = model.to_cnf()
        ids = _ids_by_name(cnf)

        for a_val in (True, False):
            for b_val in (True, False):
                assignment = {ids["ARoot"]: True, ids["A"]: a_val, ids["B"]: b_val}
                expected = a_val == b_val
                assert (
                    _cnf_satisfied(cnf.clauses, assignment) == expected
                ), f"A={a_val} B={b_val}: expected equivalence to hold={expected}"

    def test_cnf_negated_equivalence_constraint(self, backend):
        """Regression companion: negated equivalence must also parse and
        convert correctly (exercises the EQUIVALENCE case in NNF conversion,
        not just the parser)."""
        uvl_content = """features
    ARoot
        optional
            A
            B

constraints
    !(A <=> B)
"""
        model = UVL(from_str=uvl_content, backend=backend)
        cnf = model.to_cnf()
        ids = _ids_by_name(cnf)

        for a_val in (True, False):
            for b_val in (True, False):
                assignment = {ids["ARoot"]: True, ids["A"]: a_val, ids["B"]: b_val}
                expected = a_val != b_val
                assert (
                    _cnf_satisfied(cnf.clauses, assignment) == expected
                ), f"A={a_val} B={b_val}: expected XOR to hold={expected}"

    def test_to_cnf_strips_tautological_clauses(self, backend):
        """A clause containing both a literal and its negation is always
        true regardless of assignment, so it carries zero real constraint
        information -- but left in, it can confuse downstream heuristics
        that pattern-match on clause shape (e.g. any2uvl's group detection
        mistaking one for a self-referencing group, as happened on
        automotive02v4). to_cnf() must filter these out.
        """
        uvl_content = """features
    ARoot
        optional
            A
            B

constraints
    A | !A
"""
        model = UVL(from_str=uvl_content, backend=backend)
        cnf = model.to_cnf()
        for clause in cnf.clauses:
            lits = set(clause)
            assert not any(
                -lit in lits for lit in lits
            ), f"Tautological clause found in CNF output: {clause}"

    def test_aggregate_functions_detected(self, backend):
        aggregate_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "aggregate.uvl"
        )
        model = UVL(from_file=aggregate_file, backend=backend)

        constraints = model.arithmetic_constraints
        assert any("sum" in c for c in constraints), "Should detect sum() aggregate"
        assert any("avg" in c for c in constraints), "Should detect avg() aggregate"

    def test_attribute_extraction(self, backend):
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "expressions.uvl"
        )
        model = UVL(from_file=example_file, backend=backend)

        constraints_text = " ".join(model.arithmetic_constraints)
        assert "B.Price" in constraints_text
        assert "B.Fun" in constraints_text
        assert "C.Fun" in constraints_text


def test_antlr_lexer_blank_line_preserves_indent_stack():
    """Regression: uvl_custom_lexer.handleNewline() checked
    `self._input.LA(1) == "\\n"` (and "\\r", "\\f", "#") to decide whether
    to skip indentation tracking for blank/comment lines -- but LA(1)
    returns an integer character code in the antlr4 Python runtime, not a
    string, so none of those comparisons could ever be True. Every blank
    line was therefore treated as a real zero-indentation line, which
    triggered a full dedent back to depth 0 and discarded every
    shallower indent level, even ones still needed as valid ancestors for
    later content. This is a direct unit test on the lexer's indent stack
    (rather than going through the full parser) so it stays precise about
    what broke: a blank line between two same-depth siblings must not
    change the indent stack at all.
    """
    from antlr4 import InputStream
    from uvllang.antlr4.uvl_custom_lexer import uvl_custom_lexer

    content = "A\n\tB\n\t\tC\n\t\tD\n\n\t\tE\n"
    lexer = uvl_custom_lexer(InputStream(content))
    stream_tokens = []
    while True:
        t = lexer.nextToken()
        if t.type == -1:  # EOF
            break
        stream_tokens.append(t)

    # nextToken() drains the indent stack with trailing DEDENTs once EOF
    # is reached, so the final stack is always empty -- that's expected,
    # not the thing under test. What matters is the token *sequence*
    # between D and E: since they're siblings at the same depth (with
    # only a blank line between them), there must be no INDENT/DEDENT in
    # between, just the blank line's NEWLINE.
    names = [
        "EOF" if t.type == -1 else lexer.symbolicNames[t.type] for t in stream_tokens
    ]
    d_idx = next(i for i, t in enumerate(stream_tokens) if t.text == "D")
    e_idx = next(i for i, t in enumerate(stream_tokens) if t.text == "E")
    between = names[d_idx + 1 : e_idx]
    assert (
        "DEDENT" not in between and "INDENT" not in between
    ), f"blank line between same-depth siblings corrupted indentation: {between}"


def test_antlr_blank_line_mid_hierarchy_recovers_all_features():
    """End-to-end companion to test_antlr_lexer_blank_line_preserves_indent_stack:
    a blank line in the middle of a deeply nested feature tree used to
    desync the ANTLR parser (it would raise or silently truncate the rest
    of the file, expecting only EOF/'constraints' where real content
    still followed). Found via automotive02v4.uvl, where it silently
    dropped ~94% of the model's features.
    """
    uvl_content = """namespace Test

features
    Root
        mandatory
            A
                mandatory
                    B
                        optional
                            C
                            D

        optional
            E
"""
    model = UVL(from_str=uvl_content, backend="antlr")
    features = {f.strip('"') for f in model.features}
    assert features == {
        "Root",
        "A",
        "B",
        "C",
        "D",
        "E",
    }, f"Expected all 6 features, got: {features}"

    builder = model.builder()
    hierarchy = builder.feature_hierarchy
    root_info = next(
        info for name, info in hierarchy.items() if name.strip('"') == "Root"
    )
    child_names = {c.strip('"') for c, _ in root_info["children"]}
    assert (
        "A" in child_names and "E" in child_names
    ), f"Root should have both A and E as direct children, got: {child_names}"


class TestNonBooleanConstructs:
    """to_cnf() raises NonBooleanConstructError by default for constructs
    above the plain Boolean language level that would otherwise silently
    threaten the CNF's semantics (Tier 1/2 -- see
    README.md#non-boolean-constructs), but only ever warns for purely decorative
    ones (Tier 3: typed features, value attributes). Identical across all
    three backends -- parametrized over all of them, not just zig.
    Merely constructing a UVL never raises: the Boolean-only limitation is
    specific to to_cnf(), not parsing (to_smt() has no such restriction).
    """

    GROUP_CARDINALITY = """\
features
    Root
        [1..2]
            A
            B
            C
"""

    CONSTRAINT_ATTRIBUTE = """\
features
    Root {constraint A => B}
        optional
            A
            B
"""

    ATTRIBUTE_REF_CONSTRAINT = """\
features
    Root {weight 3}
        optional
            A

constraints
    Root.weight > 1
"""

    COMPARISON_CONSTRAINT = """\
features
    Root
        optional
            A

constraints
    1 > 0
"""

    TIER1_2_SOURCES = {
        "group_cardinality": GROUP_CARDINALITY,
        "constraint_attribute": CONSTRAINT_ATTRIBUTE,
        "attribute_ref": ATTRIBUTE_REF_CONSTRAINT,
        "comparison": COMPARISON_CONSTRAINT,
    }

    @pytest.mark.parametrize("backend", BACKENDS)
    @pytest.mark.parametrize(
        "source", TIER1_2_SOURCES.values(), ids=TIER1_2_SOURCES.keys()
    )
    def test_construction_never_raises(self, source, backend):
        """Only to_cnf() enforces the Boolean-only limitation."""
        model = UVL(from_str=source, backend=backend)
        assert "Root" in model.features

    @pytest.mark.parametrize("backend", BACKENDS)
    @pytest.mark.parametrize(
        "source", TIER1_2_SOURCES.values(), ids=TIER1_2_SOURCES.keys()
    )
    def test_to_cnf_raises_by_default(self, source, backend):
        model = UVL(from_str=source, backend=backend)
        with pytest.raises(NonBooleanConstructError):
            model.to_cnf()

    @pytest.mark.parametrize("backend", BACKENDS)
    @pytest.mark.parametrize(
        "source", TIER1_2_SOURCES.values(), ids=TIER1_2_SOURCES.keys()
    )
    def test_drop_non_boolean_suppresses_the_exception(self, source, backend):
        model = UVL(from_str=source, backend=backend, drop_non_boolean=True)
        cnf = model.to_cnf()
        assert cnf.clauses is not None

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_feature_cardinality_raises_by_default(self, backend):
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "feature-cardinality.uvl"
        )
        model = UVL(from_file=example_file, backend=backend)
        assert len(model.features) == 4
        with pytest.raises(NonBooleanConstructError):
            model.to_cnf()
        model2 = UVL(from_file=example_file, backend=backend, drop_non_boolean=True)
        assert len(model2.to_cnf().clauses) > 0

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_tier3_only_never_raises(self, backend):
        """automotive01.uvl has 799 value attributes (Tier 3) and no
        Tier 1/2 constructs -- must not raise, even from to_cnf(), by
        default."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=example_file, backend=backend)
        assert len(model.to_cnf().clauses) == 10311


class TestConversion:
    """conversion=True applies the UVLParser paper's conversion strategies
    for group cardinality and feature-local constraint attributes instead
    of dropping them, identically on all three backends -- see
    parser/src/cnf/conversion.zig / README.md#non-boolean-constructs."""

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_group_cardinality_no_longer_raises_under_conversion(self, backend):
        model = UVL(
            from_str=TestNonBooleanConstructs.GROUP_CARDINALITY,
            backend=backend,
            conversion=True,
        )
        cnf = model.to_cnf()
        assert cnf.clauses is not None

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_constraint_attribute_no_longer_raises_under_conversion(self, backend):
        model = UVL(
            from_str=TestNonBooleanConstructs.CONSTRAINT_ATTRIBUTE,
            backend=backend,
            conversion=True,
        )
        cnf = model.to_cnf()
        assert cnf.clauses is not None

    def test_group_cardinality_and_constraint_attribute_clauses_match_across_backends(
        self,
    ):
        """The zig-native parser and the Lark/ANTLR extractors must
        produce byte-identical CNF clause sets under conversion=True."""
        for example in ("group-cardinality.uvl", "feature-local-constraint.uvl"):
            example_file = os.path.join(
                os.path.dirname(__file__), "..", "examples", example
            )
            reference = UVL(from_file=example_file, backend="zig", conversion=True)
            ids = {f: i + 1 for i, f in enumerate(sorted(reference.features))}
            ref_clauses = {
                tuple(sorted(c)) for c in reference.to_cnf(ids).clauses
            }
            for backend in ("lark", "antlr"):
                model = UVL(from_file=example_file, backend=backend, conversion=True)
                clauses = {tuple(sorted(c)) for c in model.to_cnf(ids).clauses}
                assert clauses == ref_clauses, (example, backend)

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_group_cardinality_encoding_matches_bound(self, backend):
        """[2..3] over {FeatureA,FeatureB,FeatureC,FeatureD}: every
        satisfying assignment must select between 2 and 3 of the four."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "group-cardinality.uvl"
        )
        model = UVL(from_file=example_file, backend=backend, conversion=True)
        ids = {f: i + 1 for i, f in enumerate(sorted(model.features))}
        cnf = model.to_cnf(ids)
        members = [ids["FeatureA"], ids["FeatureB"], ids["FeatureC"], ids["FeatureD"]]

        from pysat.solvers import Glucose3

        with Glucose3(bootstrap_with=cnf.clauses) as solver:
            for bits in range(16):
                assumptions = [
                    m if (bits >> i) & 1 else -m for i, m in enumerate(members)
                ]
                sat = solver.solve(assumptions=assumptions)
                n_selected = bin(bits).count("1")
                assert sat == (2 <= n_selected <= 3), (bits, n_selected, sat)

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_feature_local_constraint_extraction_matches_top_level(self, backend):
        """A feature-local `constraint A => B` under conversion=True must
        produce the exact same clause as writing `A => B` as a top-level
        constraint."""
        top_level = """\
features
    Root
        optional
            A
            B

constraints
    A => B
"""
        local = """\
features
    Root {constraint A => B}
        optional
            A
            B
"""
        m1 = UVL(from_str=top_level, backend=backend)
        m2 = UVL(from_str=local, backend=backend, conversion=True)
        ids = {f: i + 1 for i, f in enumerate(sorted(m1.features))}
        c1 = {tuple(sorted(c)) for c in m1.to_cnf(ids).clauses}
        c2 = {tuple(sorted(c)) for c in m2.to_cnf(ids).clauses}
        assert c1 == c2

    @pytest.mark.parametrize("backend", BACKENDS)
    def test_feature_cardinality_still_raises_under_conversion(self, backend):
        """Feature cardinality is explicitly deferred future work -- see
        README.md#non-boolean-constructs -- and must keep raising even with
        conversion=True."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "feature-cardinality.uvl"
        )
        model = UVL(from_file=example_file, backend=backend, conversion=True)
        with pytest.raises(NonBooleanConstructError):
            model.to_cnf()


class TestFromCnfAndFileOutputs:
    """UVL(from_cnf=...) (any2uvl recovery as an alternate constructor),
    to_dimacs()/to_smt(filepath) (uvl2cnf/uvl2smt as file-writing methods),
    and the source/exactly-one-of validation around them."""

    UVL_SOURCE = "features\n    Root\n        mandatory\n            A\n        optional\n            B\n"

    def test_exactly_one_source_required(self):
        with pytest.raises(ValueError):
            UVL()
        with pytest.raises(ValueError):
            UVL(from_str=self.UVL_SOURCE, from_cnf="unused.dimacs")

    def test_recovery_kwargs_require_from_cnf(self):
        with pytest.raises(ValueError):
            UVL(from_str=self.UVL_SOURCE, verify=True)

    def test_from_file_rejects_non_uvl_content(self, tmp_path):
        bad = tmp_path / "bad.uvl"
        bad.write_text("p cnf 1 1\n1 0\n")
        with pytest.raises(ValueError):
            UVL(from_file=str(bad))

    def test_to_dimacs_writes_a_loadable_dimacs_file(self, tmp_path):
        model = UVL(from_str=self.UVL_SOURCE)
        out = tmp_path / "model.dimacs"
        model.to_dimacs(str(out))
        assert (
            out.read_text().splitlines()[0].startswith("c ")
            or "p cnf" in out.read_text()
        )

    def test_to_smt_writes_the_same_text_it_returns(self, tmp_path):
        model = UVL(from_str=self.UVL_SOURCE)
        text = model.to_smt()
        out = tmp_path / "model.smt2"
        assert model.to_smt(str(out)) is None
        assert out.read_text() == text

    def test_from_cnf_via_file_path_round_trips(self, tmp_path):
        model = UVL(from_str=self.UVL_SOURCE)
        dimacs_path = tmp_path / "model.dimacs"
        model.to_dimacs(str(dimacs_path))

        recovered = UVL(from_cnf=str(dimacs_path))
        assert set(recovered.features) == set(model.features)
        assert recovered.builder().root_feature == model.builder().root_feature

    def test_from_cnf_via_pysat_cnf_object_round_trips(self):
        model = UVL(from_str=self.UVL_SOURCE)
        recovered = UVL(from_cnf=model.to_cnf())
        assert set(recovered.features) == set(model.features)

    def test_from_cnf_rejects_dimacs_without_a_p_line(self, tmp_path):
        bad = tmp_path / "bad.dimacs"
        bad.write_text("1 2 0\n-1 0\n")
        with pytest.raises(ValueError):
            UVL(from_cnf=str(bad))

    def test_from_cnf_verify_reports_a_clean_pass(self):
        model = UVL(from_str=self.UVL_SOURCE)
        recovered = UVL(from_cnf=model.to_cnf(), verify=True)
        assert recovered.recovery_result == {
            "total_orig_clauses": len(model.to_cnf().clauses),
            "missing": 0,
            "extra": 0,
        }

    def test_from_cnf_without_verify_leaves_recovery_result_none(self):
        model = UVL(from_str=self.UVL_SOURCE)
        recovered = UVL(from_cnf=model.to_cnf())
        assert recovered.recovery_result is None

    def test_from_cnf_result_usable_on_any_backend(self):
        model = UVL(from_str=self.UVL_SOURCE)
        recovered = UVL(from_cnf=model.to_cnf(), backend="lark")
        assert set(recovered.features) == set(model.features)

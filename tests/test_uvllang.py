"""
Tests for the UVL Parser implementation.

These tests verify that both Lark and ANTLR parsers correctly parse UVL files
and produce consistent results.
"""

import pytest
import os
import tempfile
from uvllang import UVL
from uvllang.main import NonBooleanConstructError


def _cnf_satisfied(clauses, assignment):
    """assignment: dict of 1-based variable id -> bool. True if every clause
    has at least one satisfied literal under the given assignment."""
    return all(
        any((lit > 0) == assignment[abs(lit)] for lit in clause)
        for clause in clauses
    )


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


@pytest.mark.parametrize("use_antlr", [False, True])
@pytest.mark.parametrize(
    "example", EXAMPLE_FILES, ids=[e["file"] for e in EXAMPLE_FILES]
)
class TestUVLParsing:
    """Consolidated tests for UVL file parsing."""

    def test_uvl2cnf(self, example, use_antlr):
        """Test that file parses successfully with expected feature count."""
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
        model = UVL(
            from_file=example_file,
            backend="antlr" if use_antlr else "lark",
            drop_non_boolean=True,
        )

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


@pytest.mark.parametrize("use_antlr", [False, True])
class TestUVLFeatures:
    """Test specific UVL language features."""

    def test_parse_simple_inline_uvl(self, use_antlr):
        """Test parsing a simple inline UVL definition."""
        uvl_content = """namespace TestNS

features
    Root
        mandatory
            FeatureA
        optional
            FeatureB
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            assert model.tree is not None
            assert len(model.features) == 3
            assert "Root" in model.features
            assert "FeatureA" in model.features
            assert "FeatureB" in model.features
        finally:
            os.unlink(temp_file)

    def test_invalid_file_raises_error(self, use_antlr):
        """Test that parsing an invalid file raises an error."""
        invalid_content = "This is not valid UVL syntax!"

        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(invalid_content)
            temp_file = f.name

        try:
            with pytest.raises(Exception):
                UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
        finally:
            os.unlink(temp_file)

    def test_nonexistent_file_raises_error(self, use_antlr):
        """Test that parsing a nonexistent file raises an error."""
        with pytest.raises(FileNotFoundError):
            UVL(from_file="nonexistent_file.uvl", backend="antlr" if use_antlr else "lark")

    def test_cnf_root_constraint(self, use_antlr):
        """Test that CNF includes root feature constraint."""
        uvl_content = """namespace Test

features
    ARoot
        mandatory
            BChild
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_mandatory_constraint(self, use_antlr):
        """Test that CNF correctly encodes mandatory relationships."""
        uvl_content = """namespace Test

features
    ARoot
        mandatory
            BChild
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-2, 1] in cnf.clauses
            assert [-1, 2] in cnf.clauses
            assert len(cnf.clauses) == 3
        finally:
            os.unlink(temp_file)

    def test_cnf_optional_constraint(self, use_antlr):
        """Test that CNF correctly encodes optional relationships."""
        uvl_content = """namespace Test

features
    ARoot
        optional
            BOptionalChild
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-2, 1] in cnf.clauses
            assert len(cnf.clauses) == 2
        finally:
            os.unlink(temp_file)

    def test_cnf_xor_constraint(self, use_antlr):
        """Test that CNF correctly encodes XOR/alternative groups."""
        uvl_content = """namespace Test

features
    ARoot
        alternative
            BChildA
            CChildB
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-1, 2, 3] in cnf.clauses
            assert [-2, -3] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_or_constraint(self, use_antlr):
        """Test that CNF correctly encodes OR groups."""
        uvl_content = """namespace Test

features
    ARoot
        or
            BChildA
            CChildB
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-1, 2, 3] in cnf.clauses
            assert [-2, -3] not in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_builder_external_usage_and_feature_iteration(self, use_antlr):
        """Test that builder can be accessed externally and iterates through all features."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, backend="antlr" if use_antlr else "lark")
        builder = model.builder()

        # Test that builder can be used from outside
        assert builder is not None
        assert builder.root_feature is not None
        assert builder.feature_hierarchy is not None

        # Test that builder visits all features in the model
        builder_features = set(builder.feature_hierarchy.keys())
        model_features = set(model.features)

        # All model features should be in the builder's hierarchy
        assert builder_features == model_features
        assert len(builder_features) == 173

    def test_implication_constraints_automotive01(self, use_antlr):
        """Test that implication constraints are correctly classified as boolean."""
        automotive_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=automotive_file, backend="antlr" if use_antlr else "lark")

        # Verify that implication constraints are correctly classified as boolean
        implication_constraints = [c for c in model.boolean_constraints if "=>" in c]
        assert (
            len(implication_constraints) > 0
        ), "Should have implication (=>) constraints"

    @pytest.mark.parametrize(
        "constraint_text", ["A <=> B", "A<=>B", "A <=>B", "A<=> B"]
    )
    def test_cnf_equivalence_constraint(self, use_antlr, constraint_text):
        """Regression: <=> must not be mistaken for an arithmetic comparison.

        _constraints_to_cnf used to strip only "=>" from the constraint text
        before checking for stray comparison operators; stripping "=>" out
        of "<=>" leaves a "<" behind, which made every equivalence
        constraint get silently skipped as an "arithmetic comparison" --
        regardless of whitespace around the operator.
        """
        uvl_content = f"""namespace Test

features
    ARoot
        optional
            A
            B

constraints
    {constraint_text}
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            assert len(model.boolean_constraints) == 1
            assert len(model.arithmetic_constraints) == 0

            features2ids = {"ARoot": 1, "A": 2, "B": 3}
            cnf = model.to_cnf(features2ids=features2ids)

            for a_val in (True, False):
                for b_val in (True, False):
                    assignment = {1: True, 2: a_val, 3: b_val}
                    expected = a_val == b_val
                    assert _cnf_satisfied(cnf.clauses, assignment) == expected, (
                        f"A={a_val} B={b_val}: expected equivalence to hold={expected}"
                    )
        finally:
            os.unlink(temp_file)

    def test_cnf_negated_equivalence_constraint(self, use_antlr):
        """Regression companion: negated equivalence must also parse and
        convert correctly (exercises the EQUIVALENCE case in NNF conversion,
        not just the parser)."""
        uvl_content = """namespace Test

features
    ARoot
        optional
            A
            B

constraints
    !(A <=> B)
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            features2ids = {"ARoot": 1, "A": 2, "B": 3}
            cnf = model.to_cnf(features2ids=features2ids)

            for a_val in (True, False):
                for b_val in (True, False):
                    assignment = {1: True, 2: a_val, 3: b_val}
                    expected = a_val != b_val
                    assert _cnf_satisfied(cnf.clauses, assignment) == expected, (
                        f"A={a_val} B={b_val}: expected XOR to hold={expected}"
                    )
        finally:
            os.unlink(temp_file)

    def test_to_cnf_strips_tautological_clauses(self, use_antlr):
        """A clause containing both a literal and its negation is always
        true regardless of assignment, so it carries zero real constraint
        information -- but left in, it can confuse downstream heuristics
        that pattern-match on clause shape (e.g. any2uvl's group detection
        mistaking one for a self-referencing group, as happened on
        automotive02v4). to_cnf() must filter these out.
        """
        uvl_content = """namespace Test

features
    ARoot
        optional
            A
            B

constraints
    A | !A
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, backend="antlr" if use_antlr else "lark")
            cnf = model.to_cnf()
            for clause in cnf.clauses:
                lits = set(clause)
                assert not any(-lit in lits for lit in lits), (
                    f"Tautological clause found in CNF output: {clause}"
                )
        finally:
            os.unlink(temp_file)

    def test_aggregate_functions_detected(self, use_antlr):
        """Test that aggregate functions are detected in constraints."""
        aggregate_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "aggregate.uvl"
        )
        model = UVL(from_file=aggregate_file, backend="antlr" if use_antlr else "lark")

        constraints = model.arithmetic_constraints
        assert any("sum" in c for c in constraints), "Should detect sum() aggregate"
        assert any("avg" in c for c in constraints), "Should detect avg() aggregate"

    def test_attribute_extraction(self, use_antlr):
        """Test that feature attributes are extracted correctly."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "expressions.uvl"
        )
        model = UVL(from_file=example_file, backend="antlr" if use_antlr else "lark")

        # Check that attributes are referenced in constraints
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
    from uvllang.uvl_custom_lexer import uvl_custom_lexer

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
    names = ["EOF" if t.type == -1 else lexer.symbolicNames[t.type] for t in stream_tokens]
    d_idx = next(i for i, t in enumerate(stream_tokens) if t.text == "D")
    e_idx = next(i for i, t in enumerate(stream_tokens) if t.text == "E")
    between = names[d_idx + 1 : e_idx]
    assert "DEDENT" not in between and "INDENT" not in between, (
        f"blank line between same-depth siblings corrupted indentation: {between}"
    )


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
    with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
        f.write(uvl_content)
        temp_file = f.name

    try:
        model = UVL(from_file=temp_file, use_antlr=True)
        features = {f.strip('"') for f in model.features}
        assert features == {"Root", "A", "B", "C", "D", "E"}, (
            f"Expected all 6 features, got: {features}"
        )

        builder = model.builder()
        hierarchy = builder.feature_hierarchy
        root_info = next(
            info for name, info in hierarchy.items() if name.strip('"') == "Root"
        )
        child_names = {c.strip('"') for c, _ in root_info["children"]}
        assert "A" in child_names and "E" in child_names, (
            f"Root should have both A and E as direct children, got: {child_names}"
        )
    finally:
        os.unlink(temp_file)


BACKENDS = ["zig", "lark", "antlr"]


class TestNonBooleanConstructs:
    """to_cnf() raises NonBooleanConstructError by default for constructs
    above the plain Boolean language level that would otherwise silently
    threaten the CNF's semantics (Tier 1/2 -- see
    docs/non_boolean_support.md), but only ever warns for purely decorative
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



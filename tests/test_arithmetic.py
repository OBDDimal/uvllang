"""
Tests for arithmetic constraint parsing and SMT-LIB 2 conversion.
"""

import pytest
import os
from uvllang import UVL

BACKENDS = ["zig", "lark", "antlr"]


# Test data for SMT-related example files
SMT_EXAMPLE_FILES = [
    {
        "file": "expressions.uvl",
        "features": {"A", "B", "C"},
        "arith_constraints": 24,
        "has_attributes": True,
        "attribute_refs": ["B.Price", "B.Fun", "C.Fun"],
        "expected_sat": "sat",
        "expected_features": {"A": True},  # Root must be selected
    },
    {
        "file": "aggregate.uvl",
        "features": {"A", "B", "C"},
        "arith_constraints": 2,
        "has_attributes": True,
        "has_aggregates": ["sum", "avg"],
        "feature_attributes": {
            "A": {"Price": "1"},
            "B": {"Price": "2"},
            "C": {"Price": "5"},
        },
        "expected_sat": "sat",
        "expected_features": {"A": True},
        "expected_attributes": {"A.Price": "1", "B.Price": "2", "C.Price": "5"},
    },
    {
        "file": "aggregateFunctions.uvl",
        "features": {"A", "B", "C"},
        "arith_constraints": 2,
        "has_attributes": True,
        "has_aggregates": ["sum", "avg"],
        "feature_attributes": {
            "A": {"Price": "2"},
            "B": {"Price": "2"},
            "C": {"Price": "5"},
        },
        "expected_sat": "sat",  # sat when B is not selected: A(2) + C(5) = 7, avg = 3.5
        "expected_features": {"A": True, "C": True, "B": False},
        "expected_attributes": {"A.Price": "2", "C.Price": "5"},
    },
    {
        "file": "lengthAggregation.uvl",
        "features": {"A", "B", "C"},
        "arith_constraints": 3,
        "has_types": True,
        "has_len_function": True,
        "string_features": ["B", "C"],
        "expected_sat": "sat",
        "expected_features": {"A": True},
        "expected_string_lengths": {"B_val": 16, "C_val": 16},
    },
    {
        "file": "string-constraints.uvl",
        "features": {"A", "C", "D"},
        "arith_constraints": 4,
        "has_types": True,
        "string_features": ["C", "D"],
        "has_string_comparisons": True,  # Has string == comparisons
        "expected_sat": "sat",
        "expected_features": {"A": True},
        "expected_attributes": {
            "C_val": '"Fun"',
            "D_val": '"Fun"',
        },  # Z3 returns strings with quotes
    },
]


@pytest.mark.parametrize("backend", BACKENDS)
@pytest.mark.parametrize(
    "example", SMT_EXAMPLE_FILES, ids=[e["file"] for e in SMT_EXAMPLE_FILES]
)
class TestSMTExamples:
    """Consolidated tests for SMT example files, identically across all
    three backends."""

    def test_parse_and_classify(self, example, backend):
        """Test parsing and constraint classification."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, backend=backend)

        # Check features
        assert (
            set(model.features) == example["features"]
        ), f"{example['file']}: Expected features {example['features']}"

        # Check constraints
        assert (
            len(model.arithmetic_constraints) == example["arith_constraints"]
        ), f"{example['file']}: Expected {example['arith_constraints']} arithmetic constraints"

        # Check attributes if present
        if example.get("has_attributes"):
            if "attribute_refs" in example:
                constraints_text = " ".join(model.arithmetic_constraints)
                for ref in example["attribute_refs"]:
                    assert (
                        ref in constraints_text
                    ), f"Expected attribute reference: {ref}"

        # Check aggregates if present
        if example.get("has_aggregates"):
            constraints = model.arithmetic_constraints
            for agg in example["has_aggregates"]:
                assert any(agg in c for c in constraints), f"Expected aggregate: {agg}"

        # Check feature attributes if specified
        if "feature_attributes" in example:
            for feature, attrs in example["feature_attributes"].items():
                assert (
                    feature in model.feature_attributes
                ), f"Feature {feature} should have attributes"
                for attr_name, attr_value in attrs.items():
                    assert (
                        model.feature_attributes[feature][attr_name] == attr_value
                    ), f"Expected {feature}.{attr_name} = {attr_value}"

    def test_smt_generation(self, example, backend):
        """Test SMT-LIB 2 generation."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, backend=backend)
        smt = model.to_smt()

        # Check basic structure
        assert "; Feature declarations" in smt
        assert "(check-sat)" in smt
        assert "(get-model)" in smt

        # Check feature declarations
        for feature in example["features"]:
            assert f"(declare-const {feature} Bool)" in smt

        # Check string features if present
        if example.get("string_features"):
            for feature in example["string_features"]:
                assert f"(declare-const {feature}_val String)" in smt

            # Check for str.len if has_len_function is set
            if example.get("has_len_function"):
                for feature in example["string_features"]:
                    assert f"(str.len {feature}_val)" in smt

        # Check aggregates are expanded (no raw aggregate functions)
        if example.get("has_aggregates"):
            for agg in example["has_aggregates"]:
                assert (
                    f"{agg}(" not in smt.lower()
                ), f"Aggregate {agg}() should be expanded, not passed raw"

        # Check len() is converted to str.len
        if example.get("has_len_function"):
            assert "len(" not in smt.lower()
            assert "(str.len " in smt

    def test_z3_solving(self, example, backend):
        """Test that Z3 produces expected solutions matching our understanding."""
        try:
            from z3 import Solver, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, backend=backend)
        smt = model.to_smt()

        solver = Solver()
        solver.from_string(smt)
        result = solver.check()

        # Verify expected satisfiability
        expected = sat if example["expected_sat"] == "sat" else unsat
        assert (
            result == expected
        ), f"{example['file']}: Expected {example['expected_sat']} but got {result}"

        # If sat, validate the solution
        if result == sat:
            m = solver.model()
            model_dict = {d.name(): str(m[d]) for d in m.decls()}

            # Check expected feature selections
            for feature, expected_val in example.get("expected_features", {}).items():
                actual = model_dict.get(feature)
                assert actual == str(
                    expected_val
                ), f"{example['file']}: Feature {feature} should be {expected_val}, got {actual}"

            # Check expected attribute values
            for attr, expected_val in example.get("expected_attributes", {}).items():
                actual = model_dict.get(attr)
                assert (
                    actual == expected_val
                ), f"{example['file']}: Attribute {attr} should be {expected_val}, got {actual}"

            # Check expected string lengths
            for str_var, expected_len in example.get(
                "expected_string_lengths", {}
            ).items():
                if str_var in model_dict:
                    val_str = model_dict[str_var].strip('"')
                    assert (
                        len(val_str) == expected_len
                    ), f"{example['file']}: {str_var} should have length {expected_len}, got {len(val_str)}"


@pytest.mark.parametrize("backend", BACKENDS)
class TestSMTQuotingAndSortInference:
    """Regression tests for quoted-identifier and attribute-sort-inference
    correctness in to_smt()'s output (parser/src/smt/writer.zig, called for
    every backend). Real example models (berkeleydb.uvl, comments.uvl,
    automotive01.uvl) once produced SMT-LIB that z3 rejected outright."""

    def test_quoted_feature_name_is_a_valid_smt_symbol(self, backend):
        z3 = pytest.importorskip("z3")
        uvl_content = 'features\n    "My Root"\n        optional\n            A\n'
        model = UVL(from_str=uvl_content, backend=backend)
        smt = model.to_smt()

        assert '"My Root"' not in smt
        assert "|My Root|" in smt
        solver = z3.Solver()
        solver.from_string(smt)
        assert str(solver.check()) == "sat"

    def test_quoted_name_used_in_a_boolean_constraint(self, backend):
        """The specific pattern that broke comments.uvl: a quoted name
        used as a constraint operand, not just in a declaration."""
        z3 = pytest.importorskip("z3")
        uvl_content = (
            "features\n"
            "    Root\n"
            "        optional\n"
            '            "weird//name"\n'
            "            C\n"
            "\n"
            "constraints\n"
            '    "weird//name" => C\n'
        )
        model = UVL(from_str=uvl_content, backend=backend)
        smt = model.to_smt()
        solver = z3.Solver()
        solver.from_string(smt)
        assert str(solver.check()) == "sat"

    def test_string_valued_attribute_declared_as_string_sort(self, backend):
        z3 = pytest.importorskip("z3")
        uvl_content = "features\n    Root {tag 'v1'}\n        optional\n            A\n"
        model = UVL(from_str=uvl_content, backend=backend)
        smt = model.to_smt()

        assert "(declare-const Root.tag String)" in smt
        solver = z3.Solver()
        solver.from_string(smt)
        assert str(solver.check()) == "sat"


@pytest.mark.parametrize("backend", BACKENDS)
class TestSMTConversion:
    """SMT conversion of inline UVL definitions -- prefix-notation
    arithmetic and operator precedence."""

    def test_smt_arithmetic_operators(self, backend):
        """Test arithmetic operator conversion to prefix notation."""
        uvl_content = """features
    A
        mandatory
            B {Price 10, Fun 20}

constraints
    B.Price + B.Fun == 30
    B.Fun * 2 == 40
    B.Price - 5 == 5
    B.Fun / 2 == 10
"""
        model = UVL(from_str=uvl_content, backend=backend)
        smt = model.to_smt()

        assert "(+ B.Price B.Fun)" in smt
        assert "(* B.Fun 2)" in smt
        assert "(- B.Price 5)" in smt
        assert "(/ B.Fun 2)" in smt

    def test_smt_operator_precedence(self, backend):
        """Test that operator precedence is handled correctly."""
        uvl_content = """features
    A
        mandatory
            B {X 2, Y 3, Z 4}

constraints
    B.X + B.Y * B.Z == 14
    B.X * B.Y + B.Z == 10
"""
        model = UVL(from_str=uvl_content, backend=backend)
        smt = model.to_smt()

        # Check precedence: multiplication before addition
        assert "(+ B.X (* B.Y B.Z))" in smt
        assert "(+ (* B.X B.Y) B.Z)" in smt


# test_uvllang.py::TestFromCnfAndFileOutputs covers to_smt(filepath) itself
# (writing to a real path and reading it back); nothing here duplicates that.

# The uvl2smt CLI is now a native Zig binary (parser/zig-out/bin/uvl2smt),
# not this uvllang.cli.uvl2smt Python entry point (removed -- see
# uvllang/cli.py's module docstring). See tests/test_zig_smt.py for its
# coverage; UVL.to_smt() (exercised elsewhere in this file, for every
# backend) is a ctypes call into the same writer.

"""
Tests for arithmetic constraint parsing and SMT-LIB 2 conversion.
"""

import pytest
import os
import tempfile
from uvllang import UVL


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
        "expected_attributes": {"C_val": '"Fun"', "D_val": '"Fun"'},  # Z3 returns strings with quotes
    },
]


@pytest.mark.parametrize("use_antlr", [False, True])
@pytest.mark.parametrize(
    "example", SMT_EXAMPLE_FILES, ids=[e["file"] for e in SMT_EXAMPLE_FILES]
)
class TestSMTExamples:
    """Consolidated tests for SMT example files."""

    def test_parse_and_classify(self, example, use_antlr):
        """Test parsing and constraint classification."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)

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

    def test_smt_generation(self, example, use_antlr):
        """Test SMT-LIB 2 generation."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)
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

    def test_z3_solving(self, example, use_antlr):
        """Test that Z3 produces expected solutions matching our understanding."""
        try:
            from z3 import Solver, sat, unsat
        except ImportError:
            pytest.skip("z3-solver not installed")

        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)
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


@pytest.mark.parametrize("use_antlr", [False, True])
class TestSMTConversion:
    """Test SMT conversion with inline UVL definitions."""

    def test_smt_arithmetic_operators(self, use_antlr):
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
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
            smt = model.to_smt()

            # Check operators are converted to prefix notation
            assert "(+ B.Price B.Fun)" in smt
            assert "(* B.Fun 2)" in smt
            assert "(- B.Price 5)" in smt
            assert "(/ B.Fun 2)" in smt

        finally:
            os.unlink(temp_file)

    def test_smt_operator_precedence(self, use_antlr):
        """Test that operator precedence is handled correctly."""
        uvl_content = """features
    A
        mandatory
            B {X 2, Y 3, Z 4}

constraints
    B.X + B.Y * B.Z == 14
    B.X * B.Y + B.Z == 10
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
            smt = model.to_smt()

            # Check precedence: multiplication before addition
            assert "(+ B.X (* B.Y B.Z))" in smt
            assert "(+ (* B.X B.Y) B.Z)" in smt

        finally:
            os.unlink(temp_file)

    def test_smt_file_output(self, use_antlr):
        """Test writing SMT to file and reading it back."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "expressions.uvl"
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)
        smt = model.to_smt()

        with tempfile.NamedTemporaryFile(mode="w", suffix=".smt2", delete=False) as f:
            f.write(smt)
            temp_file = f.name

        try:
            with open(temp_file, "r") as f:
                content = f.read()

            assert content == smt
            assert "(check-sat)" in content

        finally:
            os.unlink(temp_file)


class TestCLISMT:
    """Test the uvl2smt CLI tool."""

    def test_cli_smt_basic(self):
        """Test basic CLI functionality for SMT conversion."""
        from uvllang.cli import uvl2smt
        import sys

        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "expressions.uvl"
        )

        with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False) as f:
            output_file = f.name

        try:
            # Simulate CLI call
            old_argv = sys.argv
            sys.argv = ["uvl2smt", example_file, output_file]

            try:
                uvl2smt()
            except SystemExit:
                pass

            # Check output file was created
            assert os.path.exists(output_file)

            with open(output_file, "r") as f:
                content = f.read()

            assert "(check-sat)" in content
            assert "(declare-const A Bool)" in content

        finally:
            sys.argv = old_argv
            if os.path.exists(output_file):
                os.unlink(output_file)

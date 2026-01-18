"""
Tests for the UVL Parser implementation.

These tests verify that both Lark and ANTLR parsers correctly parse UVL files
and produce consistent results.
"""

import pytest
import os
import tempfile
from uvllang import UVL


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

    def test_parse_file(self, example, use_antlr):
        """Test that file parses successfully with expected feature count."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)

        assert model.tree is not None, f"{example['file']} should parse successfully"
        assert (
            len(model.features) == example["features"]
        ), f"{example['file']} should have {example['features']} features"

    def test_constraint_classification(self, example, use_antlr):
        """Test that constraints are classified correctly."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)

        assert (
            len(model.boolean_constraints) == example["bool_constraints"]
        ), f"{example['file']} should have {example['bool_constraints']} boolean constraints"
        assert (
            len(model.arithmetic_constraints) == example["arith_constraints"]
        ), f"{example['file']} should have {example['arith_constraints']} arithmetic constraints"

    def test_cnf_conversion(self, example, use_antlr):
        """Test CNF conversion"""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", example["file"]
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)
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
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
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
                UVL(from_file=temp_file, use_antlr=use_antlr)
        finally:
            os.unlink(temp_file)

    def test_nonexistent_file_raises_error(self, use_antlr):
        """Test that parsing a nonexistent file raises an error."""
        with pytest.raises(FileNotFoundError):
            UVL(from_file="nonexistent_file.uvl", use_antlr=use_antlr)

    def test_cnf_root_constraint(self, use_antlr):
        """Test that CNF includes root feature constraint."""
        uvl_content = """namespace Test

features
    Root
        mandatory
            Child
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_mandatory_constraint(self, use_antlr):
        """Test that CNF correctly encodes mandatory relationships."""
        uvl_content = """namespace Test

features
    Root
        mandatory
            Child
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-1, 2] in cnf.clauses
            assert [-2, 1] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_optional_constraint(self, use_antlr):
        """Test that CNF correctly encodes optional relationships."""
        uvl_content = """namespace Test

features
    Root
        optional
            OptionalChild
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
            cnf = model.to_cnf()
            assert [1] in cnf.clauses
            assert [-2, 1] in cnf.clauses
            assert [-1, 2] not in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_xor_constraint(self, use_antlr):
        """Test that CNF correctly encodes XOR/alternative groups."""
        uvl_content = """namespace Test

features
    Root
        alternative
            ChildA
            ChildB
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
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
    Root
        or
            ChildA
            ChildB
"""
        with tempfile.NamedTemporaryFile(mode="w", suffix=".uvl", delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file, use_antlr=use_antlr)
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
        model = UVL(from_file=eshop_file, use_antlr=use_antlr)
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
        model = UVL(from_file=automotive_file, use_antlr=use_antlr)

        # Verify that implication constraints are correctly classified as boolean
        implication_constraints = [c for c in model.boolean_constraints if "=>" in c]
        assert (
            len(implication_constraints) > 0
        ), "Should have implication (=>) constraints"

    def test_aggregate_functions_detected(self, use_antlr):
        """Test that aggregate functions are detected in constraints."""
        aggregate_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "aggregate.uvl"
        )
        model = UVL(from_file=aggregate_file, use_antlr=use_antlr)

        constraints = model.arithmetic_constraints
        assert any("sum" in c for c in constraints), "Should detect sum() aggregate"
        assert any("avg" in c for c in constraints), "Should detect avg() aggregate"

    def test_attribute_extraction(self, use_antlr):
        """Test that feature attributes are extracted correctly."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "expressions.uvl"
        )
        model = UVL(from_file=example_file, use_antlr=use_antlr)

        # Check that attributes are referenced in constraints
        constraints_text = " ".join(model.arithmetic_constraints)
        assert "B.Price" in constraints_text
        assert "B.Fun" in constraints_text
        assert "C.Fun" in constraints_text

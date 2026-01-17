"""
Tests for the Lark-based UVL Parser implementation.

These tests verify that the Lark grammar correctly parses UVL files
and maintains compatibility with the ANTLR implementation.
"""

import pytest
import os
import tempfile
from uvllang.main import UVL


class TestLarkUVLParser:
    """Test cases for Lark-based UVL parsing functionality."""

    def test_parse_automotive01_uvl(self):
        """Test parsing the automotive01 UVL file."""
        example_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=example_file, parser_type="lark")

        assert model.tree is not None
        assert len(model.features) == 2513

    def test_parse_eshop_uvl(self):
        """Test parsing the eshop UVL file."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, parser_type="lark")

        assert model.tree is not None
        assert len(model.features) == 173
        assert "eShop" in model.features

    def test_parse_simple_uvl(self):
        """Test parsing a simple UVL file."""
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
            model = UVL(from_file=temp_file, parser_type="lark")
            assert model.tree is not None
            assert len(model.features) == 3
            assert "Root" in model.features
            assert "FeatureA" in model.features
            assert "FeatureB" in model.features
        finally:
            os.unlink(temp_file)

    def test_invalid_file_raises_error(self):
        """Test that parsing an invalid file raises an error."""
        invalid_content = "This is not valid UVL syntax!"

        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
            f.write(invalid_content)
            temp_file = f.name

        try:
            with pytest.raises(Exception):
                UVL(from_file=temp_file, parser_type="lark")
        finally:
            os.unlink(temp_file)

    def test_nonexistent_file_raises_error(self):
        """Test that parsing a nonexistent file raises an error."""
        with pytest.raises(FileNotFoundError):
            UVL(from_file="nonexistent_file.uvl", parser_type="lark")

    def test_constraint_classification_eshop(self):
        """Test that eshop.uvl has only arithmetic constraints (no boolean)."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, parser_type="lark")

        assert (
            len(model.arithmetic_constraints) == 0
        ), "eshop should have 0 arithmetic constraints"
        assert (
            len(model.boolean_constraints) == 0
        ), "eshop should have 0 boolean constraints"

    def test_constraint_classification_automotive01(self):
        """Test that automotive01.uvl has 2833 boolean constraints."""
        automotive_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=automotive_file, parser_type="lark")

        assert (
            len(model.boolean_constraints) == 2833
        ), "automotive01 should have 2833 boolean constraints"
        assert (
            len(model.arithmetic_constraints) == 0
        ), "automotive01 should have 0 arithmetic constraints"

        # Verify that implication constraints are correctly classified as boolean
        implication_constraints = [c for c in model.boolean_constraints if "=>" in c]
        assert (
            len(implication_constraints) > 0
        ), "Should have implication (=>) constraints"


class TestLarkCNFConversion:
    """Test cases for CNF conversion functionality with Lark parser."""

    def test_cnf_eshop(self):
        """Test CNF conversion for eshop.uvl."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, parser_type="lark")
        cnf = model.to_cnf()

        assert len(cnf.clauses) == 289
        assert cnf.nv == 173
        assert all(isinstance(clause, list) for clause in cnf.clauses)
        assert all(isinstance(lit, int) for clause in cnf.clauses for lit in clause)

    def test_cnf_automotive01(self):
        """Test CNF conversion for automotive01.uvl."""
        auto_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "automotive01.uvl"
        )
        model = UVL(from_file=auto_file, parser_type="lark")
        cnf = model.to_cnf()

        assert len(cnf.clauses) == 10311
        assert cnf.nv == 2513
        assert all(isinstance(clause, list) for clause in cnf.clauses)
        assert all(isinstance(lit, int) for clause in cnf.clauses for lit in clause)

    def test_cnf_root_constraint(self):
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
            model = UVL(from_file=temp_file, parser_type="lark")
            cnf = model.to_cnf()

            assert [1] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_mandatory_constraint(self):
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
            model = UVL(from_file=temp_file, parser_type="lark")
            cnf = model.to_cnf()

            assert [1] in cnf.clauses
            assert [-1, 2] in cnf.clauses
            assert [-2, 1] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_optional_constraint(self):
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
            model = UVL(from_file=temp_file, parser_type="lark")
            cnf = model.to_cnf()

            assert [1] in cnf.clauses
            assert [-2, 1] in cnf.clauses
            assert [-1, 2] not in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_xor_constraint(self):
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
            model = UVL(from_file=temp_file, parser_type="lark")
            cnf = model.to_cnf()

            assert [1] in cnf.clauses
            assert [-1, 2, 3] in cnf.clauses
            assert [-2, -3] in cnf.clauses
        finally:
            os.unlink(temp_file)

    def test_cnf_or_constraint(self):
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
            model = UVL(from_file=temp_file, parser_type="lark")
            cnf = model.to_cnf()

            assert [1] in cnf.clauses
            assert [-1, 2, 3] in cnf.clauses
            assert [-2, -3] not in cnf.clauses
        finally:
            os.unlink(temp_file)


class TestLarkBuilder:
    """Test cases for the Lark FeatureModelBuilder functionality."""

    def test_builder_external_usage_and_feature_iteration(self):
        """Test that builder can be accessed externally and iterates through all features."""
        eshop_file = os.path.join(
            os.path.dirname(__file__), "..", "examples", "eshop.uvl"
        )
        model = UVL(from_file=eshop_file, parser_type="lark")
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

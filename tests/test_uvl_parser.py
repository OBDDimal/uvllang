"""
Tests for the UVL Parser package.
"""

import pytest
import os
import tempfile
from uvllang.main import UVL


class TestUVLParser:
    """Test cases for UVL parsing functionality."""

    def test_parse_automotive01_uvl(self):
        """Test parsing the automotive01 UVL file."""
        example_file = os.path.join(os.path.dirname(__file__), '..', 'examples', 'automotive01.uvl')
        model = UVL(from_file=example_file)
        
        assert model.tree is not None
        assert len(model.features) == 2513
        assert model.tree.getText().startswith('namespace')

    def test_parse_eshop_uvl(self):
        """Test parsing the eshop UVL file."""
        eshop_file = os.path.join(os.path.dirname(__file__), '..', 'examples', 'eshop.uvl')
        model = UVL(from_file=eshop_file)
        
        assert model.tree is not None
        assert len(model.features) == 173
        assert 'eShop' in model.features

    def test_parse_simple_uvl(self):
        """Test parsing a simple UVL file."""
        uvl_content = '''namespace TestNS

features
    Root
        mandatory
            FeatureA
        optional
            FeatureB
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            assert model.tree is not None
            assert len(model.features) == 3
            assert 'Root' in model.features
            assert 'FeatureA' in model.features
            assert 'FeatureB' in model.features
        finally:
            os.unlink(temp_file)

    def test_invalid_file_raises_error(self):
        """Test that parsing an invalid file raises an error."""
        invalid_content = 'This is not valid UVL syntax!'
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
            f.write(invalid_content)
            temp_file = f.name

        try:
            with pytest.raises(Exception):
                UVL(from_file=temp_file)
        finally:
            os.unlink(temp_file)

    def test_nonexistent_file_raises_error(self):
        """Test that parsing a nonexistent file raises an error."""
        with pytest.raises(FileNotFoundError):
            UVL(from_file='nonexistent_file.uvl')


class TestCNFConversion:
    """Test cases for CNF conversion functionality."""

    def test_cnf_eshop(self):
        """Test CNF conversion for eshop.uvl."""
        eshop_file = os.path.join(os.path.dirname(__file__), '..', 'examples', 'eshop.uvl')
        model = UVL(from_file=eshop_file)
        cnf = model.to_cnf()
        
        assert len(cnf) == 289
        assert len(model.features) == 173
        assert all(isinstance(clause, list) for clause in cnf)
        assert all(isinstance(lit, int) for clause in cnf for lit in clause)

    def test_cnf_automotive01(self):
        """Test CNF conversion for automotive01.uvl."""
        auto_file = os.path.join(os.path.dirname(__file__), '..', 'examples', 'automotive01.uvl')
        model = UVL(from_file=auto_file)
        cnf = model.to_cnf()
        
        assert len(cnf) == 10311
        assert len(model.features) == 2513
        assert all(isinstance(clause, list) for clause in cnf)
        assert all(isinstance(lit, int) for clause in cnf for lit in clause)

    def test_cnf_root_constraint(self):
        """Test that CNF includes root feature constraint."""
        uvl_content = '''namespace Test

features
    Root
        mandatory
            Child
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            cnf = model.to_cnf()
            
            assert [1] in cnf
        finally:
            os.unlink(temp_file)

    def test_cnf_mandatory_constraint(self):
        """Test that CNF correctly encodes mandatory relationships."""
        uvl_content = '''namespace Test

features
    Root
        mandatory
            Child
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            cnf = model.to_cnf()
            
            assert [1] in cnf
            assert [-1, 2] in cnf
            assert [-2, 1] in cnf
        finally:
            os.unlink(temp_file)

    def test_cnf_optional_constraint(self):
        """Test that CNF correctly encodes optional relationships."""
        uvl_content = '''namespace Test

features
    Root
        optional
            OptionalChild
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            cnf = model.to_cnf()
            
            assert [1] in cnf
            assert [-2, 1] in cnf
            assert [-1, 2] not in cnf
        finally:
            os.unlink(temp_file)

    def test_cnf_xor_constraint(self):
        """Test that CNF correctly encodes XOR/alternative groups."""
        uvl_content = '''namespace Test

features
    Root
        alternative
            ChildA
            ChildB
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            cnf = model.to_cnf()
            
            assert [1] in cnf
            assert [-1, 2, 3] in cnf
            assert [-2, -3] in cnf
        finally:
            os.unlink(temp_file)

    def test_cnf_or_constraint(self):
        """Test that CNF correctly encodes OR groups."""
        uvl_content = '''namespace Test

features
    Root
        or
            ChildA
            ChildB
'''
        with tempfile.NamedTemporaryFile(mode='w', suffix='.uvl', delete=False) as f:
            f.write(uvl_content)
            temp_file = f.name

        try:
            model = UVL(from_file=temp_file)
            cnf = model.to_cnf()
            
            assert [1] in cnf
            assert [-1, 2, 3] in cnf
            assert [-2, -3] not in cnf
        finally:
            os.unlink(temp_file)
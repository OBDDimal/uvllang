# uvllang

A Python parser for the Universal Variability Language (UVL) with support for both Lark (default, pure Python) and ANTLR4 parsers.

## Installation

```bash
# Install with Lark parser (default, pure Python)
pip install uvllang

# Install with both Lark and ANTLR parsers
pip install uvllang[antlr]
```

## Usage

### Basic Usage

```python
from uvllang import UVL

# Parse a UVL file with Lark (default)
model = UVL(from_file="examples/automotive01.uvl")

# Or use ANTLR parser
model = UVL(from_file="examples/automotive01.uvl", parser_type="antlr")

# Access features
print(f"Number of features:", len(model.features))

# Access constraints
print("All constraints:", len(model.constraints))
print("Boolean constraints:", len(model.boolean_constraints))
print("Arithmetic constraints:", len(model.arithmetic_constraints))
```

### CNF Conversion

Convert feature models to Conjunctive Normal Form (CNF) for SAT solvers:

```python
from uvllang import UVL

# Parse UVL file
model = UVL(from_file="model.uvl")

# Convert to CNF (returns PySAT CNF object)
cnf = model.to_cnf()
cnf.to_file("output.dimacs")
```

### Command Line Interface

The CLI uses **Lark by default** (pure Python, no external dependencies):

```bash
# Install basic version (Lark only)
pip install uvllang

# Basic conversion (uses Lark)
uvl2cnf model.uvl

# Specify output file
uvl2cnf model.uvl output.dimacs

# Verbose mode (lists ignored constraints)
uvl2cnf model.uvl -v

# Use ANTLR parser (requires: pip install uvllang[antlr])
uvl2cnf model.uvl --antlr
```

## Dependencies

**Core dependencies** (always installed):
- `lark`: Lark parser (default, pure Python)
- `sympy`: Symbolic mathematics for Boolean constraint processing
- `python-sat`: SAT solver library for CNF handling

**Optional dependencies**:
- `antlr4-python3-runtime`: ANTLR4 parser runtime (install with: `pip install uvllang[antlr]`)

Both parsers provide identical functionality. Lark is used by default for easier installation and pure Python compatibility.

## Testing

```bash
# Install development dependencies
pip install -e .[dev]

# Run tests
python -m pytest tests/
```

## Development

```bash
# Generate parsers from grammar files
python generate_parsers.py

# Build package
python build_package.py

# Or build manually
python -m build
```

## Citation

If you use UVL in your research, please cite:

```bibtex
@article{UVL2024,
  title     = {UVL: Feature modelling with the Universal Variability Language},
  journal   = {Journal of Systems and Software},
  volume    = {225},
  pages     = {112326},
  year      = {2025},
  doi       = {https://doi.org/10.1016/j.jss.2024.112326},
  author    = {David Benavides and Chico Sundermann and Kevin Feichtinger and José A. Galindo and Rick Rabiser and Thomas Thüm}
}
```

## Links

- [UVL Models Repository](https://github.com/Universal-Variability-Language/uvl-models)
- [UVL Website](https://universal-variability-language.github.io/)

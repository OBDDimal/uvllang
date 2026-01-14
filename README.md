# uvllang

A Python parser for the Universal Variability Language (UVL). Based on ANTLR4, adopted from https://github.com/Universal-Variability-Language/uvl-parser.

## Installation

```bash
pip install uvllang
```

## Usage

### Parsing

```python
from uvllang.main import UVL

# Parse a UVL file
model = UVL(from_file="examples/automotive01.uvl")

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
from uvllang.main import UVL

# Parse UVL file
model = UVL(from_file="model.uvl")

# Convert to CNF (returns PySAT CNF object)
cnf = model.to_cnf()
cnf.to_file("output.dimacs")
```

### Command Line Interface

```bash
uvl2cnf --help

# Basic conversion
uvl2cnf model.uvl

# Specify output file
uvl2cnf model.uvl output.dimacs

# Verbose mode (lists ignored constraints)
uvl2cnf model.uvl -v
```

## Dependencies

- `antlr4-python3-runtime`: ANTLR4 parser runtime
- `sympy`: Symbolic mathematics for Boolean constraint processing
- `python-sat`: SAT solver library for CNF handling

## Testing

```bash
# Install development dependencies
pip install -e .

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

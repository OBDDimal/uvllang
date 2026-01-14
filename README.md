# uvllang

A Python parser for the Universal Variability Language (UVL) based on ANTLR4.

## Installation

```bash
pip install uvllang
```

## Usage

### Basic Parsing

```python
from uvl.main import UVL

# Parse a UVL file
model = UVL(from_file="path/to/file.uvl")

# Access features
features = model.features
print(f"Number of features: {len(features)}")

# Access constraints
constraints = model.constraints
```

### CNF Conversion

Convert feature models to Conjunctive Normal Form (CNF) for SAT solvers:

```python
from uvllang.main import UVL

# Parse UVL file
model = UVL(from_file="model.uvl")

# Convert to CNF
cnf_clauses = model.to_cnf()

# Export to DIMACS format
with open("output.dimacs", 'w') as f:
    f.write(f"p cnf {len(model.features)} {len(cnf_clauses)}\n")
    for clause in cnf_clauses:
        f.write(' '.join(map(str, clause)) + ' 0\n')
```

Or use the command-line tool:

```bash
# Convert UVL to DIMACS (saves to current directory)
uvl2cnf model.uvl

# Specify output file
uvl2cnf model.uvl output.dimacs
```

The CNF conversion supports:
- Mandatory and optional features
- OR groups (at least one child)
- XOR/Alternative groups (exactly one child)
- Cross-tree constraints (using sympy)

### Backward Compatibility

```python
import uvl

# Legacy API still supported
tree = uvl.get_tree("path/to/file.uvl")
features = uvl.get_features("path/to/file.uvl")
constraints = uvl.get_constraints("path/to/file.uvl")
```

## Testing

```bash
# Install development dependencies
pip install -e ".[dev]"

# Run tests
python -m pytest tests/
```

## Packaging (For Developers)

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

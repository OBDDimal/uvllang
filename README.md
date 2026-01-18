# uvllang

A Python parser for the Universal Variability Language (UVL) with support for both Lark (default) and ANTLR parsers. In addition, `uvllang` supports conversion of UVL to CNF / SMT.

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
model = UVL(from_file="examples/automotive01.uvl", use_antlr = True)

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

### SMT-LIB 2 Conversion

Convert feature models to SMT-LIB 2 format for SMT solvers (supports arithmetic constraints, types, and aggregates):

```python
from uvllang import UVL

# Parse UVL file with arithmetic constraints
model = UVL(from_file="model.uvl")

# Convert to SMT-LIB 2 format
smt_content = model.to_smt()

# Save to file
with open("output.smt2", "w") as f:
    f.write(smt_content)

# Or use Z3 directly
import z3

solver = z3.Solver()
solver.from_string(smt_content)
result = solver.check()

print(result)  # sat, unsat, or unknown
```

**SMT-LIB 2 Features:**
- Boolean feature selection constraints
- Arithmetic constraints with integer and real types
- String features and length constraints
- Aggregate functions: `sum(attr)`, `avg(attr)`, `len(feature)`
- Feature attributes and typed declarations

### Command Line Interface

```bash
# Basic conversion (uses Lark)
uvl2cnf model.uvl

# Specify output file
uvl2cnf model.uvl output.dimacs

# Verbose mode (lists ignored non-Boolean constraints)
uvl2cnf model.uvl -v

# Use ANTLR parser (requires: pip install uvllang[antlr])
uvl2cnf model.uvl --antlr
```

**SMT-LIB 2 conversion:**

```bash
# Basic conversion (uses Lark)
uvl2smt model.uvl

# Specify output file
uvl2smt model.uvl output.smt2

# Verbose mode (shows model statistics)
uvl2smt model.uvl -v

# Use ANTLR parser
uvl2smt model.uvl --antlr

# Solve with Z3
uvl2smt model.uvl model.smt2 && z3 model.smt2
```

## Dependencies

**Core dependencies** (always installed):
- `lark`: Lark parser
- `sympy`: Symbolic mathematics for Boolean constraint processing
- `python-sat`: SAT solver library for CNF handling

**Optional dependencies**:
- `antlr4-python3-runtime`: ANTLR4 parser runtime (install with: `pip install uvllang[antlr]`)
- `z3-solver`: Z3 SMT solver for solving SMT-LIB 2 constraints (install with: `pip install z3-solver`)

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
# Generate parsers from grammar files (ANTLR)
python generate_parsers.py

# Build
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

- [Official UVL Parser](https://github.com/Universal-Variability-Language/uvl-parser)
- [UVL Models Repository](https://github.com/Universal-Variability-Language/uvl-models)
- [UVL Website](https://universal-variability-language.github.io/)

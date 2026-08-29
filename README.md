<p align="center">
  <img src="logo.svg" alt="uvllang logo" width="220" />
</p>

# uvllang

A parser for the Universal Variability Language (UVL). Supports conversion to CNF (DIMACS), SMT-LIB 2, and recovery of UVL models from DIMACS files.

`uvl2cnf` is a native Zig binary with no Python involved. The Python API (`UVL(...)`) defaults to the same Zig backend, and also supports `backend="lark"`/`"antlr"` for full feature/attribute extraction parity, or as a second reference implementation.

## Installation

```bash
pip install uvllang

# With ANTLR parser support (backend="antlr" in the Python API)
pip install uvllang[antlr]
```

The Zig backend (the `uvl2cnf` binary, and the Python API's default) needs building once: `cd parser && zig build`. Then symlink the binary onto your PATH, e.g. `ln -s ../../parser/zig-out/bin/uvl2cnf .venv/bin/uvl2cnf`.

## CLI tools

### uvl2cnf — UVL to DIMACS CNF

A native binary (`parser/zig-out/bin/uvl2cnf`, built by `zig build` in `parser/`) with no Python involved, not even at startup.

```bash
uvl2cnf model.uvl                 # writes model.dimacs
uvl2cnf model.uvl output.dimacs   # explicit output path
uvl2cnf model.uvl -v              # accepted; ignored-constraint info already prints unconditionally
```

For Lark/ANTLR specifically (e.g. cross-checking against this backend), use the Python API instead: `UVL(from_file="model.uvl", backend="lark").to_cnf()`.

Only the plain **Boolean** language level is supported for CNF conversion, identically across all three backends — group cardinality (`[i..j]` groups), feature-local `{constraint ...}` attributes, and feature cardinality (clone multiplicity) all threaten the CNF's correctness if silently ignored, which is what happens today (see [`docs/non_boolean_support.md`](docs/non_boolean_support.md)). `uvl2cnf` always warns and continues regardless; `to_cnf()` in the Python API raises `NonBooleanConstructError` by default for those three plus dropped constraints (attribute-reference/comparison), unless you pass `drop_non_boolean=True` to `UVL(...)`. `to_smt()` has no such restriction and never raises. Typed features and unreferenced value attributes are always just warned about, never raised on.

### uvl2smt — UVL to SMT-LIB 2

```bash
uvl2smt model.uvl                 # writes model.smt2
uvl2smt model.uvl output.smt2
uvl2smt model.uvl -v              # show model statistics
uvl2smt model.uvl --antlr
```

### any2uvl — DIMACS CNF to UVL

Recovers a UVL feature model from a DIMACS file. Hierarchy is reconstructed via a spanning-tree heuristic; remaining clauses become cross-tree constraints.

```bash
any2uvl model.dimacs              # writes model_recovered.uvl
any2uvl model.dimacs output.uvl
any2uvl --optimize model.dimacs   # run CTC-reduction optimiser after recovery
any2uvl --byname model.dimacs     # break hierarchy tie-breaks by feature name similarity
```

The `--optimize` pass groups features that share common implied parents and moves them into the hierarchy, reducing cross-tree constraints where valid (verified by DIMACS equivalence check).

`--byname` affects the initial spanning-tree construction: when two candidate parents are at equal depth, the one whose name is most similar to the child (by edit-distance ratio) wins. Combine with `--optimize` for best results.

## Python API

```python
from uvllang import UVL

model = UVL(from_file="model.uvl")

# CNF (PySAT CNF object)
cnf = model.to_cnf()
cnf.to_file("output.dimacs")

# SMT-LIB 2
smt = model.to_smt()
with open("output.smt2", "w") as f:
    f.write(smt)

# DIMACS → UVL recovery
UVL.from_cnf("model.dimacs", "recovered.uvl", optimize=True, by_name=True)
```

## Dependencies

- `lark` — backend="lark" in the Python API
- `python-sat` — CNF handling
- `antlr4-python3-runtime` — optional, backend="antlr" in the Python API and `uvl2smt`/`any2uvl`'s `--antlr`
- `z3-solver` — optional, for solving SMT output

## Testing

```bash
pip install -e .[dev]
pytest tests/
```

## Citation

```bibtex
@article{UVL2024,
  title   = {UVL: Feature modelling with the Universal Variability Language},
  journal = {Journal of Systems and Software},
  volume  = {225},
  pages   = {112326},
  year    = {2025},
  doi     = {https://doi.org/10.1016/j.jss.2024.112326},
  author  = {David Benavides and Chico Sundermann and Kevin Feichtinger and José A. Galindo and Rick Rabiser and Thomas Thüm}
}
```

## Links

- [UVL Parser](https://github.com/Universal-Variability-Language/uvl-parser)
- [UVL Models](https://github.com/Universal-Variability-Language/uvl-models)
- [UVL Website](https://universal-variability-language.github.io/)

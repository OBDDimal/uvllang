<p align="center">
  <img src="logo.svg" alt="uvllang logo" width="220" />
</p>

# uvllang

A parser for the Universal Variability Language (UVL). Supports conversion to CNF (DIMACS), SMT-LIB 2, and recovery of UVL models from DIMACS files.

`uvl2cnf`, `uvl2uvl`, `uvl2smt`, and `any2uvl` are all native Zig binaries with no Python involved. The Python API (`UVL(...)`) defaults to the same Zig backend, and also supports `backend="lark"`/`"antlr"` for full feature/attribute extraction parity, or as a second reference implementation.

## Installation

```bash
pip install uvllang

# With Lark parser support (backend="lark" in the Python API)
pip install uvllang[lark]

# With ANTLR parser support (backend="antlr" in the Python API)
pip install uvllang[antlr]
```

The Zig backend (all four binaries above, and the Python API's default) needs building once: `cd parser && zig build`. Then symlink the binaries onto your PATH, e.g. `ln -s ../../parser/zig-out/bin/uvl2cnf .venv/bin/uvl2cnf` (repeat for `uvl2uvl`/`uvl2smt`/`any2uvl`).

## CLI tools

### uvl2cnf — UVL to DIMACS CNF

A native binary (`parser/zig-out/bin/uvl2cnf`, built by `zig build` in `parser/`) with no Python involved, not even at startup.

```bash
uvl2cnf model.uvl                 # writes model.dimacs
uvl2cnf model.uvl output.dimacs   # explicit output path
uvl2cnf model.uvl -v              # accepted; ignored-constraint info already prints unconditionally
uvl2cnf --conversion model.uvl    # convert group cardinality + feature-local constraint attributes instead of dropping them
```

For Lark/ANTLR specifically (e.g. cross-checking against this backend), use the Python API instead: `UVL(from_file="model.uvl", backend="lark").to_cnf()`.

Only the plain **Boolean** language level is supported for CNF conversion, identically across all three backends — group cardinality (`[i..j]` groups), feature-local `{constraint ...}` attributes, and feature cardinality (clone multiplicity) all threaten the CNF's correctness if silently ignored, which is what happens by default (see [`docs/non_boolean_support.md`](docs/non_boolean_support.md)). `--conversion` (CLI) / `conversion=True` (Python API, all three backends) applies the UVLParser paper's conversion strategies for the first two of these instead of dropping them; feature cardinality is documented future work, not built. `uvl2cnf` always warns and continues regardless of `--conversion`; `to_cnf()` in the Python API raises `NonBooleanConstructError` by default for group/feature cardinality and feature-local constraint attributes plus dropped constraints (attribute-reference/comparison), unless you pass `drop_non_boolean=True` to `UVL(...)` — `conversion=True` removes group cardinality and constraint attributes from that raising set, since they're actually handled at that point. `to_smt()` has no such restriction and never raises. Typed features and unreferenced value attributes are always just warned about, never raised on.

### uvl2smt — UVL to SMT-LIB 2

A native binary (`parser/zig-out/bin/uvl2smt`), unlike `uvl2cnf` not restricted to the plain Boolean level: numeric comparisons, aggregate functions (`sum`/`avg`/`len`/`floor`/`ceil`, including the 2-argument scoped form `sum(Feature, Attr)`), and typed (`String`/`Integer`/`Real`) features are all represented.

```bash
uvl2smt model.uvl                 # writes model.smt2
uvl2smt model.uvl output.smt2
uvl2smt model.uvl -v              # accepted for CLI-convention compatibility
```

The legacy Lark/ANTLR-backed `uvl2smt` CLI (with its `--antlr` flag) has been replaced by this native binary; that code path is still reachable programmatically via `UVL(backend="lark"/"antlr").to_smt()`.

### any2uvl — DIMACS CNF or SMT-LIB 2 to UVL

A native binary (`parser/zig-out/bin/any2uvl`) that recovers a UVL feature model from either a DIMACS CNF file or an `.smt2` file written by `uvl2smt` (input format is detected from content, not the file extension — general, arbitrary SMT-LIB 2 files from other tools aren't supported). Hierarchy is reconstructed via a spanning-tree heuristic; remaining clauses (or, for SMT-LIB input, any assert that isn't a pure Boolean formula over declared features) become cross-tree constraints. The output is always logically equivalent to the input regardless of hierarchy-recovery quality.

```bash
any2uvl model.dimacs              # writes model_recovered.uvl
any2uvl model.smt2 output.uvl     # SMT-LIB input works the same way
any2uvl --optimize model.dimacs   # run CTC-reduction optimiser after recovery
any2uvl --byname model.dimacs     # break hierarchy tie-breaks by feature name similarity
any2uvl --verify model.dimacs     # reparse the output and confirm DIMACS equivalence (DIMACS input only)
```

The `--optimize` pass groups features that share common implied parents and moves them into the hierarchy, reducing cross-tree constraints where valid (verified by DIMACS equivalence check).

`--byname` affects the initial spanning-tree construction: when two candidate parents are at equal depth, the one whose name is most similar to the child (by edit-distance ratio) wins. Combine with `--optimize` for best results.

For SMT-LIB input, a non-Boolean assert (an arithmetic constraint, an attribute-value binding) is preserved as a residual UVL constraint when it has a UVL constraint-syntax equivalent; the small slice that doesn't (`ite`, `to_int`, `str.len` — mainly `uvl2smt`'s own aggregate-function expansions) is dropped with a warning rather than emitted as invalid UVL. `--verify` is DIMACS-only and is skipped (with a warning) for SMT-LIB input.

## Python API

```python
from uvllang import UVL

model = UVL(from_file="model.uvl")

# CNF (uvl2cnf), written straight to a DIMACS file
model.to_dimacs("output.dimacs")
cnf = model.to_cnf()  # or as a PySAT CNF object

# SMT-LIB 2 (uvl2smt) -- returns text, or writes a file if given a path
smt = model.to_smt()
model.to_smt("output.smt2")

# DIMACS -> UVL recovery (any2uvl), as an alternate constructor: from a
# file path, or directly from a pysat.formula.CNF object
recovered = UVL(from_cnf="model.dimacs", optimize=True, by_name=True)
recovered = UVL(from_cnf=cnf, verify=True)
print(recovered.recovery_result)  # {"total_orig_clauses", "missing", "extra"}
```

## Dependencies

- `lark` — backend="lark" in the Python API
- `python-sat` — CNF handling
- `antlr4-python3-runtime` — optional, `backend="antlr"` in the Python API
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

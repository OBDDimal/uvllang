<img src="logo.svg" alt="uvllang" width="100%" />

# uvllang

A parser for the Universal Variability Language (UVL). Supports conversion to CNF (DIMACS), SMT-LIB 2, and recovery of UVL models from DIMACS/SMT-LIB files.

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
uvl2cnf model.uvl -v              # also print feature/constraint/variable/clause counts
uvl2cnf --conversion model.uvl    # convert group cardinality + feature-local constraint attributes instead of dropping them
uvl2cnf --loud model.uvl          # fail instead of warning when a construct above the Boolean level would be dropped
uvl2cnf --simplify model.uvl      # run subsumption elimination over the output clause set
```

For Lark/ANTLR specifically (e.g. cross-checking against this backend), use the Python API instead: `UVL(from_file="model.uvl", backend="lark").to_cnf()`.

Only the plain **Boolean** language level is supported for CNF conversion, identically across all three backends — see [Non-Boolean constructs](#non-boolean-constructs) below for exactly what's affected and how `--conversion`/`--loud` change the behavior.

### uvl2uvl — UVL to UVL, redundant constraints removed

A native binary (`parser/zig-out/bin/uvl2uvl`) that writes a semantically equivalent UVL model back out, keeping the input's feature hierarchy exactly as-is while dropping any cross-tree constraint that's entirely subsumed by the hierarchy and the other constraints — every surviving constraint is emitted verbatim.

```bash
uvl2uvl model.uvl                 # writes model_reduced.uvl
uvl2uvl model.uvl output.uvl      # explicit output path
uvl2uvl model.uvl -v              # also print feature/constraint counts
```

### uvl2smt — UVL to SMT-LIB 2

A native binary (`parser/zig-out/bin/uvl2smt`), unlike `uvl2cnf` not restricted to the plain Boolean level: numeric comparisons, aggregate functions (`sum`/`avg`/`len`/`floor`/`ceil`, including the 2-argument scoped form `sum(Feature, Attr)`), and typed (`String`/`Integer`/`Real`) features are all represented. Feature-local `constraint`/`constraints` attributes are always included too (unconditionally, alongside the top-level `constraints` block) — SMT-LIB has no Boolean-only ceiling that would make them need a `--conversion`-style flag the way `uvl2cnf` does.

```bash
uvl2smt model.uvl                 # writes model.smt2
uvl2smt model.uvl output.smt2
uvl2smt model.uvl -v              # also print feature/constraint counts and output size
```

Lark/ANTLR-backed SMT generation is reachable programmatically via `UVL(backend="lark"/"antlr").to_smt()`, but not through this CLI.

### any2uvl — DIMACS CNF or SMT-LIB 2 to UVL

A native binary (`parser/zig-out/bin/any2uvl`) that recovers a UVL feature model from either a DIMACS CNF file or an `.smt2` file written by `uvl2smt` (input format is detected from content, not the file extension — general, arbitrary SMT-LIB 2 files from other tools aren't supported). Hierarchy is reconstructed via a spanning-tree heuristic; remaining clauses (or, for SMT-LIB input, any assert that isn't a pure Boolean formula over declared features) become cross-tree constraints. The output is always logically equivalent to the input regardless of hierarchy-recovery quality.

```bash
any2uvl model.dimacs              # writes model_recovered.uvl
any2uvl model.smt2 output.uvl     # SMT-LIB input works the same way
any2uvl --optimize model.dimacs   # run CTC-reduction optimiser after recovery
any2uvl --byname model.dimacs     # break hierarchy tie-breaks by feature name similarity
any2uvl -v model.dimacs           # also print input variable/clause counts and output constraint count
```

The `--optimize` pass groups features that share common implied parents and moves them into the hierarchy, reducing cross-tree constraints where valid.

`--byname` affects the initial spanning-tree construction: when two candidate parents are at equal depth, the one whose name is most similar to the child (by edit-distance ratio) wins. Combine with `--optimize` for best results.

For SMT-LIB input, a non-Boolean assert (an arithmetic constraint, an attribute-value binding) is preserved as a residual UVL constraint when it has a UVL constraint-syntax equivalent; the small slice that doesn't (`ite`, `to_int`, `str.len` — mainly `uvl2smt`'s own aggregate-function expansions) is dropped with a warning rather than emitted as invalid UVL.

There used to be an `any2uvl --verify` flag (and a matching `UVL(from_cnf=..., verify=True)`) that re-parsed the output and compared its CNF against the input as an exact clause set. It's removed: that comparison is unsound by construction — a logically equivalent clause set that's merely syntactically different (e.g. after `--optimize`'s subsumption cleanup) reports a false FAIL, so a real defect and a harmless rewrite are indistinguishable without a SAT-based check. `tests/test_recovery_quality.py` verifies recovery correctness properly (SAT-based equivalence via pysat), which is where that kind of check belongs.

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
recovered = UVL(from_cnf=cnf)
```

## Non-Boolean constructs

CNF conversion (`uvl2cnf`, `UVL.to_cnf()`/`to_dimacs()`) only supports the plain **Boolean** language level, identically across all three backends. Everything above that level falls into one of three tiers:

- **Tier 1 — corrupts CNF correctness, or loses a real constraint, unless converted:**
  - group cardinality (`[i..j]` groups) — the `[i..j]` bound isn't enforced in the CNF by default
  - feature-local `{constraint ...}`/`{constraints [...]}` attributes — dropped by default
  - feature cardinality (clone multiplicity) — not encoded; see [Feature cardinality: why it's not converted](#feature-cardinality-why-its-not-converted)
- **Tier 2 — a constraint is dropped entirely:**
  - a constraint referencing a feature attribute (e.g. `Feature.attr > 3`)
  - a constraint containing a numeric comparison
- **Tier 3 — decorative metadata, never affects correctness:**
  - typed (`String`/`Integer`/`Real`) features — the type itself is ignored for CNF purposes
  - value attributes on features — ignored for CNF purposes

`uvl2cnf` always warns about all three tiers and continues regardless of flags. `UVL.to_cnf()`/`to_dimacs()` raise `NonBooleanConstructError` by default for Tier 1 and Tier 2 (Tier 3 only ever warns), unless you pass `drop_non_boolean=True` to `UVL(...)`.

`--conversion` (CLI) / `conversion=True` (Python API, all three backends) applies the [UVLParser paper](#citation)'s conversion strategies for group cardinality and feature-local constraint attributes instead of dropping them — encoding the cardinality bound as enumerated Boolean clauses, and extracting the feature-local constraints as ordinary top-level constraints. With `conversion=True`, those two categories no longer raise (they're actually handled); feature cardinality still does, since it isn't converted. `uvl2cnf --loud` mirrors this exactly: it exits nonzero instead of only warning, under the same rules.

`to_smt()` has no such restriction and never raises — every construct above is representable in SMT-LIB 2.

### Feature cardinality: why it's not converted

The UVLParser paper's own prescribed strategy for feature cardinality ("repeated subtrees for feature instances", citing Czarnecki & Kim) requires cloning a whole subtree per instance and rewriting any cross-tree constraint that references a cloned feature to target a specific instance — the paper itself notes its interaction with cross-tree constraints "is not always clear," citing two disagreeing sources. This is a substantially larger and riskier piece of work than the other two conversions, so it's documented here as future work rather than built; `--conversion`/`conversion=True` never touch it.

## CNF clause-set simplification

`uvl2cnf --simplify` / `UVL.to_cnf(simplify=True)` runs a global simplification pass over the generated clause set: **subsumption elimination** (a clause entirely implied by a shorter one already present is removed) and, unless disabled, **self-subsuming resolution / strengthening** (a clause is rewritten to drop a literal made redundant by another clause), run to a fixpoint. Both are exact logical-equivalence transformations — the same satisfying assignments over the same variables, not merely equisatisfiability — so this is not a soundness trade-off.

It's **off by default** because self-subsuming resolution rewrites surviving clauses' literal content, which breaks any downstream consumer relying on a specific syntactic shape. `any2uvl`'s hierarchy reconstruction is exactly such a consumer: it finds parent/child edges by pattern-matching the plain 2-literal clause `{-child, parent}` a mandatory/optional relationship produces. If that literal clause has been subsumed away (e.g. because `parent` turns out to be forced true unconditionally by other clauses) or rewritten by SSR, the edge is missed even though the implication still holds logically. `any2uvl` does include a separate, opt-in recovery path for exactly this case (`--optimize`'s propagation-based implication check via unit propagation, which checks actual logical entailment instead of pattern-matching), but the default pipeline never runs `--simplify` upstream of it.

`UVL.to_cnf()` defaults to the same unsimplified behavior as the CLI, so the Python API and `uvl2cnf` produce the same clause set for the same input unless the caller explicitly opts in on both sides.

## Pyodide / WebAssembly

`libuvlparser.so` (the same C ABI the native Python API binds to via ctypes) can also be built for `wasm32-emscripten` and loaded inside [Pyodide](https://pyodide.org/), whose `ctypes.CDLL` is patched to `dlopen` Emscripten side modules. `uvllang/_zig.py` needs no Pyodide-specific code for this — its path search and `ctypes.CDLL(path)` call are format-agnostic. The 4 CLI binaries aren't part of this build (no subprocess model in a browser, and Zig's std start code has no wasm32-emscripten entry point to build them against), and neither are the legacy `backend="lark"`/`"antlr"` Python packages (dead weight where `backend="zig"` is the only one that matters) — `setup.py` drops both post-build for a Pyodide wheel specifically, shrinking it to ~96KB compressed.

```bash
cd parser
zig build -Dpyodide=true --sysroot "$(em-config CACHE)/sysroot" -Doptimize=ReleaseSmall
```

Requires an emscripten install (`em-config` on PATH). Produces `zig-out/lib/libuvlparser.so`. `setup.py`'s build step runs this automatically when `PYODIDE=1` is set (the signal `pyodide-build` sets in its own build environment), in place of the native build.

This needs two `capi.zig`-side workarounds for gaps in Zig 0.16's `wasm32-emscripten` support (gated on `builtin.target.cpu.arch.isWasm()`, so the native build is unaffected; see [ziglang/zig#25856](https://github.com/ziglang/zig/issues/25856) for the upstream issue): `std.heap.smp_allocator` needs real threads Emscripten doesn't provide here, so it's swapped for `std.heap.page_allocator`; and Zig's default debug-I/O backend (`std.Io.Threaded`, needed even by unrelated code such as a bare `std.StringHashMap`, since it's the default panic/debug machinery linked into every build) depends on a `getrandom` binding `std/posix.zig` doesn't define for the `.emscripten` OS tag, so it's overridden with `std.Io.failing` (compiles for every target; only errors if actually used at runtime, which this build never does).

The library is built by shelling out to `zig build-lib` directly (`parser/build.zig`'s `buildPyodideLib`) rather than through `b.addLibrary`/`b.installArtifact`, because `wasm-ld` itself still marks `-shared` output as unstable and prints a warning on every such link — and `zig build`'s own `Compile` step treats any linker stderr it doesn't recognize as a hard failure, with no build.zig-level way to allow it through. A plain subprocess invocation isn't subject to that check and produces a correct binary despite the warning.

Verified end to end (`tests/test_pyodide_wasm.py`) by instantiating the built module directly in Node with hand-provided `memory`/`__indirect_function_table`/`__stack_pointer`/`__memory_base`/`__table_base` imports — exactly what Pyodide's own dynamic linker provides for a side module — and calling `uvl_source_to_cnf` on real UVL source: it returns a correct DIMACS CNF. The module's only imports are those five standard relocatable-module primitives; it needs no libc/Emscripten runtime calls.

`libuvlparser.so` is bundled as real `package_data` (`uvllang/_zig_libs/`, populated by `setup.py`'s build hook before packaging), so a wheel built this way is installable and functional on its own — see [Releasing](#releasing) for the full `pyodide build` flow that produces a properly `pyemscripten_*_wasm32`-tagged wheel.

## Dependencies

- `python-sat` — CNF handling
- `lark` — optional (`uvllang[lark]`), `backend="lark"` in the Python API
- `antlr4-python3-runtime` — optional (`uvllang[antlr]`), `backend="antlr"` in the Python API
- `z3-solver` — optional, for solving SMT output

## Testing

```bash
pip install -e .[dev]
pytest tests/
```

## Releasing

`scripts/release.sh` builds everything `twine upload` needs — the sdist, the native wheel, a manylinux-repaired copy of it, and the Pyodide/wasm32 wheel — into `dist/`, validated with `twine check`. It doesn't upload anything; review `dist/` and run `twine upload dist/*` yourself.

```bash
pip install auditwheel patchelf pyodide-build   # patchelf ships a bundled binary, no system package needed
pyodide xbuildenv install-emscripten            # pyodide-build's own correctly-pinned Emscripten --
                                                 # do NOT rely on a system/distro emscripten package,
                                                 # it will almost certainly be the wrong version
scripts/release.sh
```

No manylinux container needed here specifically: the CLI binaries and `libuvlparser.so` are Zig's default fully-static/no-external-`NEEDED` output, so `auditwheel repair` has nothing to bundle and just re-tags the wheel — confirmed via `auditwheel show`, which already rates the plain build `manylinux_2_5_x86_64`-compatible. That's specific to this project's own binaries, not a general manylinux shortcut.

The script aborts before building anything if a required tool for either non-native step is missing, rather than silently producing a partial `dist/` — pass `--skip-manylinux`/`--skip-pyodide` to opt out of a step on purpose instead.

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

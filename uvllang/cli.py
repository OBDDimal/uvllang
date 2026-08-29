#!/usr/bin/env python3
"""
No CLI tools live here anymore -- uvl2cnf, uvl2uvl, uvl2smt, and any2uvl
are all pure native binaries (parser/zig-out/bin/{uvl2cnf,uvl2uvl,uvl2smt,
any2uvl}, built by `zig build` in parser/) with no Python involved at
all, not even at startup.

See uvllang.main.UVL(...).to_cnf()/.to_smt()/.from_cnf(...) for the
equivalent Python API, which supports backend="lark"/"antlr" in addition
to the zig default -- the legacy Lark/ANTLR-backed uvl2smt CLI this
module used to provide is still reachable that way
(UVL(backend="lark"/"antlr").to_smt()), just not as its own command
anymore.

uvl2uvl reads a UVL model and writes a semantically equivalent UVL model
back out, keeping the input's feature hierarchy exactly as-is while
dropping any cross-tree constraint that's fully redundant given the
hierarchy and the other constraints (see `uvl2uvl --help`).

any2uvl recovers a UVL feature model from a DIMACS CNF file or an
SMT-LIB 2 file (the dialect uvl2smt itself writes) -- see
`any2uvl --help`.
"""

"""
Recovery quality tests for any2uvl on the BerkeleyDB feature model.

Thresholds are set to the current known-good values so regressions are caught.

The `uvl2cnf` CLI's global clause-set simplification pass (subsumption
elimination; see docs/pipeline_clause_dedup.md) is opt-in via `--simplify`
and off by default specifically because its canonical output literal order
(and, if ever enabled, self-subsuming resolution) breaks any2uvl's hierarchy
reconstruction, which depends on hierarchy edges surviving as
untouched/positionally-stable clauses. The fixture below intentionally does
not pass `--simplify`, so parent/group recovery works as before.

`UVL.to_cnf()` (the Python API, via `capi.zig`) now defaults to the same
unsimplified behavior as the CLI (a `simplify=True` kwarg opts in, mirroring
`--simplify`), so the two entry points produce the same clause set for the
same input by default -- the DIMACS-equivalence tests below no longer need
an xfail for that reason.

`_dimacs_equivalent` checks genuine logical equivalence via SAT, not exact
clause-set identity: `any2uvl --optimize` also runs a subsumption cleanup
pass over the final residual CTCs (recovery.zig), which can legitimately
drop a CTC that another surviving clause already subsumes -- the recovered
and original clause sets can then differ while still being exactly
equivalent formulas.
"""

import os
import subprocess
import tempfile

import pytest
from pysat.formula import CNF

from uvllang import UVL

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VENV_BIN = os.path.join(ROOT, ".venv", "bin")
BERKELEYDB_UVL = os.path.join(ROOT, "examples", "berkeleydb.uvl")

REAL_GROUP_TYPES = {"or", "xor"}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _run(cmd):
    result = subprocess.run(
        cmd, capture_output=True, text=True,
        env={**os.environ, "PATH": VENV_BIN + ":" + os.environ.get("PATH", "")},
    )
    assert result.returncode == 0, f"{' '.join(cmd)} failed:\n{result.stderr}"


def _norm(name):
    return name.strip().strip('"').strip()


def _extract_hierarchy(uvl_file):
    uvl = UVL(from_file=uvl_file)
    builder = uvl.builder()
    parents, groups = {}, {}
    for feature, info in builder.feature_hierarchy.items():
        fn = _norm(feature)
        for child, _ in info["children"]:
            parents[_norm(child)] = fn
        for group_type, members in info["groups"]:
            if group_type not in REAL_GROUP_TYPES:
                continue
            ms = frozenset(_norm(m) for m in members)
            for m in ms:
                parents[m] = fn
            groups[fn] = (group_type, ms)
    return parents, groups


def _entailed(solver, clause):
    """True iff `solver`'s clause set entails `clause` (unsat with every
    literal of `clause` negated as an assumption)."""
    return not solver.solve(assumptions=[-l for l in clause])


def _dimacs_equivalent(uvl_file, dimacs_file):
    # orig_cnf and rec_cnf each assign their own ids (whatever produced
    # dimacs_file numbered it its own way; UVL.to_cnf() always numbers
    # alphabetically) -- both carry a "c <id> <name>" mapping in their
    # comments, so clauses are compared by name, renumbered here onto one
    # shared, freshly assigned id space.
    orig_cnf = CNF(from_file=dimacs_file)
    orig_id_to_name = {
        int(parts[1]): parts[2]
        for parts in (c.strip().split(None, 2) for c in orig_cnf.comments)
        if len(parts) >= 3
    }

    rec_cnf = UVL(from_file=uvl_file).to_cnf()
    rec_id_to_name = {
        int(ident): name for _, ident, name in (c.split(" ", 2) for c in rec_cnf.comments)
    }

    names = sorted(set(orig_id_to_name.values()) | set(rec_id_to_name.values()))
    ids = {name: i + 1 for i, name in enumerate(names)}

    def _renumbered(clauses, id_to_name):
        return frozenset(
            tuple(
                sorted(
                    ids[id_to_name[lit]] if lit > 0 else -ids[id_to_name[-lit]]
                    for lit in clause
                )
            )
            for clause in clauses
        )

    orig = _renumbered(orig_cnf.clauses, orig_id_to_name)
    rec = _renumbered(rec_cnf.clauses, rec_id_to_name)
    missing = orig - rec
    extra = rec - orig

    if not missing and not extra:
        return True, 0, 0

    from pysat.solvers import Glucose3

    ok = True
    if missing:
        with Glucose3(bootstrap_with=[list(c) for c in rec]) as solver:
            if not all(_entailed(solver, c) for c in missing):
                ok = False
    if extra:
        with Glucose3(bootstrap_with=[list(c) for c in orig]) as solver:
            if not all(_entailed(solver, c) for c in extra):
                ok = False

    return ok, len(missing), len(extra)


# ---------------------------------------------------------------------------
# Fixture: generate all files once per test session
# ---------------------------------------------------------------------------

@pytest.fixture(scope="session")
def recovery_files():
    with tempfile.TemporaryDirectory() as tmp:
        dimacs    = os.path.join(tmp, "berkeleydb.dimacs")
        baseline  = os.path.join(tmp, "berkeleydb_recovered.uvl")
        optimized = os.path.join(tmp, "berkeleydb_optimized.uvl")

        _run(["uvl2cnf", BERKELEYDB_UVL, dimacs])
        _run(["any2uvl", dimacs, baseline])
        _run(["any2uvl", "--optimize", dimacs, optimized])

        orig_parents, orig_groups = _extract_hierarchy(BERKELEYDB_UVL)
        base_parents, base_groups = _extract_hierarchy(baseline)
        opt_parents,  opt_groups  = _extract_hierarchy(optimized)

        yield {
            "dimacs":        dimacs,
            "baseline":      baseline,
            "optimized":     optimized,
            "orig_parents":  orig_parents,
            "orig_groups":   orig_groups,
            "base_parents":  base_parents,
            "base_groups":   base_groups,
            "opt_parents":   opt_parents,
            "opt_groups":    opt_groups,
            "base_ctcs":     len(UVL(from_file=baseline).boolean_constraints),
            "opt_ctcs":      len(UVL(from_file=optimized).boolean_constraints),
        }


# ---------------------------------------------------------------------------
# DIMACS equivalence
# ---------------------------------------------------------------------------

def test_baseline_dimacs_equivalence(recovery_files):
    ok, missing, extra = _dimacs_equivalent(
        recovery_files["baseline"], recovery_files["dimacs"]
    )
    assert ok, f"Baseline DIMACS mismatch: missing={missing} extra={extra}"


def test_optimized_dimacs_equivalence(recovery_files):
    ok, missing, extra = _dimacs_equivalent(
        recovery_files["optimized"], recovery_files["dimacs"]
    )
    assert ok, f"Optimized DIMACS mismatch: missing={missing} extra={extra}"


# ---------------------------------------------------------------------------
# Parent-child placement accuracy
# ---------------------------------------------------------------------------

def test_baseline_parent_accuracy(recovery_files):
    orig, rec = recovery_files["orig_parents"], recovery_files["base_parents"]
    correct = sum(1 for c, p in orig.items() if rec.get(c) == p)
    total   = len(orig)
    wrong   = [(c, p, rec.get(c)) for c, p in orig.items() if rec.get(c) != p]
    assert correct >= 65, (
        f"Baseline parent accuracy {correct}/{total} below threshold 65.\n"
        + "\n".join(f"  {c}: expected {p}, got {r}" for c, p, r in wrong)
    )


def test_optimized_parent_accuracy(recovery_files):
    orig, rec = recovery_files["orig_parents"], recovery_files["opt_parents"]
    correct = sum(1 for c, p in orig.items() if rec.get(c) == p)
    total   = len(orig)
    wrong   = [(c, p, rec.get(c)) for c, p in orig.items() if rec.get(c) != p]
    assert correct >= 68, (
        f"Optimized parent accuracy {correct}/{total} below threshold 68.\n"
        + "\n".join(f"  {c}: expected {p}, got {r}" for c, p, r in wrong)
    )


def test_optimized_better_than_baseline(recovery_files):
    orig = recovery_files["orig_parents"]
    base_correct = sum(1 for c, p in orig.items() if recovery_files["base_parents"].get(c) == p)
    opt_correct  = sum(1 for c, p in orig.items() if recovery_files["opt_parents"].get(c) == p)
    assert opt_correct >= base_correct, (
        f"Optimizer regressed: {opt_correct} correct vs baseline {base_correct}"
    )


# ---------------------------------------------------------------------------
# OR/XOR group recovery
# ---------------------------------------------------------------------------

def test_baseline_groups(recovery_files):
    orig, rec = recovery_files["orig_groups"], recovery_files["base_groups"]
    correct_type    = sum(1 for p, (ot, _) in orig.items() if p in rec and rec[p][0] == ot)
    correct_members = sum(1 for p, (_, om) in orig.items() if p in rec and rec[p][1] == om)
    assert correct_type    == len(orig), f"Baseline group types: {correct_type}/{len(orig)}"
    assert correct_members == len(orig), f"Baseline group members: {correct_members}/{len(orig)}"


def test_optimized_groups(recovery_files):
    orig, rec = recovery_files["orig_groups"], recovery_files["opt_groups"]
    correct_type    = sum(1 for p, (ot, _) in orig.items() if p in rec and rec[p][0] == ot)
    correct_members = sum(1 for p, (_, om) in orig.items() if p in rec and rec[p][1] == om)
    assert correct_type    == len(orig), f"Optimized group types: {correct_type}/{len(orig)}"
    assert correct_members == len(orig), f"Optimized group members: {correct_members}/{len(orig)}"


# ---------------------------------------------------------------------------
# CTC count
# ---------------------------------------------------------------------------

def test_optimized_ctcs_not_worse(recovery_files):
    assert recovery_files["opt_ctcs"] <= recovery_files["base_ctcs"], (
        f"Optimizer increased CTCs: {recovery_files['opt_ctcs']} > {recovery_files['base_ctcs']}"
    )

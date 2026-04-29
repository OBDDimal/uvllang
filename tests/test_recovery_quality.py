"""
Recovery quality tests for any2uvl on the BerkeleyDB feature model.

Thresholds are set to the current known-good values so regressions are caught.
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


def _dimacs_equivalent(uvl_file, dimacs_file):
    orig_cnf = CNF(from_file=dimacs_file)
    ids2features = {}
    for comment in orig_cnf.comments:
        parts = comment.strip().split(None, 2)
        if len(parts) >= 3:
            ids2features[int(parts[1])] = parts[2]
    features2ids = {v: k for k, v in ids2features.items()}

    rec_clauses = UVL(from_file=uvl_file).to_cnf(features2ids).clauses
    orig = frozenset(tuple(sorted(c)) for c in orig_cnf.clauses)
    rec  = frozenset(tuple(sorted(c)) for c in rec_clauses)
    return orig == rec, len(orig - rec), len(rec - orig)


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
    assert correct >= 69, (
        f"Optimized parent accuracy {correct}/{total} below threshold 69.\n"
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

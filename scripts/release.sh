#!/usr/bin/env bash
# Builds everything `twine upload` needs: the sdist, a manylinux-repaired
# native wheel, and a Pyodide/wasm32 wheel -- all left in dist/, validated
# with `twine check`. Aborts up front, before building anything, if a
# required tool for either non-native step is missing -- a silently
# incomplete dist/ (e.g. no wasm wheel, with no indication why) is worse
# than a loud failure. Pass --skip-manylinux/--skip-pyodide to opt out of
# a step on purpose instead of having it available.
#
# Does not upload anything. Once dist/ looks right, run yourself:
#   twine upload dist/*
#
# Usage: scripts/release.sh [--skip-manylinux] [--skip-pyodide]

set -euo pipefail
cd "$(dirname "$0")/.."

skip_manylinux=0
skip_pyodide=0
for arg in "$@"; do
    case "$arg" in
        --skip-manylinux) skip_manylinux=1 ;;
        --skip-pyodide) skip_pyodide=1 ;;
        *) echo "unknown argument: $arg" >&2; exit 1 ;;
    esac
done

if [ "$skip_manylinux" = 0 ] && ! command -v auditwheel >/dev/null 2>&1; then
    cat <<'EOF' >&2
error: auditwheel not found -- can't produce a manylinux-tagged wheel.
  Install with: pip install auditwheel, and run this script inside a
  manylinux container (https://github.com/pypa/manylinux) so the repair
  step checks against the right glibc baseline.
  Pass --skip-manylinux to build only a linux_x86_64-tagged wheel instead.
EOF
    exit 1
fi

# `pyodide build` manages its own Emscripten (via its xbuildenv, see
# below) independently of whatever's on PATH -- it does NOT use a system
# emcc/em-config, so there's nothing to detect or fall back to here
# beyond the `pyodide` CLI itself being installed.
if [ "$skip_pyodide" = 0 ] && ! command -v pyodide >/dev/null 2>&1; then
    cat <<'EOF' >&2
error: pyodide-build not found -- can't produce the Pyodide wheel.
  Install with: pip install pyodide-build
  Then install its own (correctly-versioned) Emscripten -- do not rely on
  a system/distro package, which is very likely a mismatched version:
    pyodide xbuildenv install-emscripten
  (see README.md#pyodide--webassembly).
  Pass --skip-pyodide to build only the native wheel(s) instead.
EOF
    exit 1
fi

# uvllang/_zig_libs/ is build output (setup.py's _bundle_lib() populates
# it as a side effect so package_data can ship it -- see uvllang/_zig.py's
# module docstring), not source -- clean up whatever's left over from a
# previous run before starting, and again on exit regardless of outcome,
# so it never lingers in the working tree between release builds (its
# presence doesn't break a dev checkout's own `zig build` -- _zig.py
# checks parser/zig-out/lib first specifically for this -- but a stale
# leftover here is still confusing to find later).
trap 'rm -rf uvllang/_zig_libs' EXIT
rm -rf dist build ./*.egg-info uvllang/_zig_libs
mkdir -p dist

echo "==> sdist + native wheel (python -m build)"
python3 -m build

if [ "$skip_manylinux" = 0 ]; then
    echo "==> repairing native wheel for manylinux (auditwheel)"
    for whl in dist/*.whl; do
        auditwheel repair "$whl" -w dist/
    done
fi

if [ "$skip_pyodide" = 0 ]; then
    echo "==> Pyodide/wasm32 wheel (pyodide build)"
    pyodide build

    # `pyodide build` runs `zig build -Dpyodide=true` directly in parser/,
    # which overwrites parser/zig-out/lib/libuvlparser.so with the wasm
    # build. Rebuild the native one so a dev checkout's own `import
    # uvllang` (which looks in parser/zig-out/lib first -- see
    # uvllang/_zig.py) isn't left pointed at a wasm .so after this script
    # finishes.
    echo "==> restoring native libuvlparser.so (parser/zig-out/lib)"
    (cd parser && zig build)
fi

echo "==> twine check"
python3 -m twine check dist/*

echo
echo "dist/ is ready -- nothing was uploaded. Review it, then run:"
echo "    twine upload dist/*"
ls -la dist/

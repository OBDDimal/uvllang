"""ctypes bindings for the Zig backend (parser/src/capi.zig).

Three entry points:
  - `parse_source_to_cnf`: full pipeline (lex/parse/build/CNF) on raw UVL
    source text, used when Python doesn't parse the file at all.
  - `hierarchy_to_cnf`: only the CNF-generation step, for a hierarchy and
    constraint list already extracted by Python (ANTLR or Lark).
  - `dimacs_to_uvl`: CNF -> UVL recovery (any2uvl).

The first two return `(clauses, id_to_name)`, the shape `UVL.to_cnf` needs
to build a `pysat.formula.CNF`. `dimacs_to_uvl` returns UVL text.
"""

import ctypes
import os

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_LIB_DIR = os.path.join(_ROOT, "parser", "zig-out", "lib")
_LIB_NAMES = ("libuvlparser.so", "libuvlparser.dylib", "uvlparser.dll")

_NO_ROOT = ctypes.c_size_t(-1).value


class _CEdge(ctypes.Structure):
    _fields_ = [
        ("parent_idx", ctypes.c_size_t),
        ("child_idx", ctypes.c_size_t),
        ("mandatory", ctypes.c_uint8),
    ]


class _CGroup(ctypes.Structure):
    _fields_ = [
        ("parent_idx", ctypes.c_size_t),
        ("kind", ctypes.c_uint8),
        ("member_start", ctypes.c_size_t),
        ("member_count", ctypes.c_size_t),
    ]


def _load_lib():
    for name in _LIB_NAMES:
        path = os.path.join(_LIB_DIR, name)
        if os.path.exists(path):
            lib = ctypes.CDLL(path)
            break
    else:
        raise RuntimeError(
            "Zig backend not built, run `zig build` in parser/ "
            f"(expected one of {_LIB_NAMES} in {_LIB_DIR})"
        )

    lib.uvl_last_error.restype = ctypes.c_char_p
    lib.uvl_last_error.argtypes = []

    lib.uvl_free_buffer.restype = None
    lib.uvl_free_buffer.argtypes = [ctypes.c_void_p, ctypes.c_size_t]

    lib.uvl_source_to_cnf.restype = ctypes.c_int32
    lib.uvl_source_to_cnf.argtypes = [
        ctypes.c_char_p,
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_size_t),
    ]

    lib.uvl_hierarchy_to_cnf.restype = ctypes.c_int32
    lib.uvl_hierarchy_to_cnf.argtypes = [
        ctypes.POINTER(ctypes.c_char_p),
        ctypes.c_size_t,
        ctypes.c_size_t,
        ctypes.POINTER(_CEdge),
        ctypes.c_size_t,
        ctypes.POINTER(_CGroup),
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_size_t),
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_char_p),
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_size_t),
    ]

    lib.uvl_dimacs_to_uvl.restype = ctypes.c_int32
    lib.uvl_dimacs_to_uvl.argtypes = [
        ctypes.c_char_p,
        ctypes.c_size_t,
        ctypes.c_uint8,
        ctypes.c_uint8,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_size_t),
    ]

    return lib


_lib = None


def _get_lib():
    global _lib
    if _lib is None:
        _lib = _load_lib()
    return _lib


def _check(lib, rc):
    if rc != 0:
        raise ValueError(lib.uvl_last_error().decode("utf-8"))


def _parse_dimacs(data: bytes):
    """DIMACS bytes -> (clauses: list[list[int]], id_to_name: dict[int, str])."""
    clauses = []
    id_to_name = {}
    for line in data.split(b"\n"):
        if not line:
            continue
        if line.startswith(b"c "):
            _, ident, name = line.decode("utf-8").split(" ", 2)
            id_to_name[int(ident)] = name
        elif line.startswith(b"p ") or not line.strip():
            continue
        else:
            lits = [int(x) for x in line.split() if x != b"0"]
            clauses.append(lits)
    return clauses, id_to_name


def _take_dimacs_buffer(lib, out_ptr, out_len):
    try:
        return _parse_dimacs(ctypes.string_at(out_ptr, out_len.value))
    finally:
        lib.uvl_free_buffer(out_ptr, out_len)


def parse_source_to_cnf(source: str):
    """Full pipeline: UVL source text -> (clauses, id_to_name)."""
    lib = _get_lib()
    src_bytes = source.encode("utf-8")
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    rc = lib.uvl_source_to_cnf(
        src_bytes, len(src_bytes), ctypes.byref(out_ptr), ctypes.byref(out_len)
    )
    _check(lib, rc)
    return _take_dimacs_buffer(lib, out_ptr, out_len)


def hierarchy_to_cnf(features, root, feature_hierarchy, constraints):
    """Only the CNF-generation step, on an already-parsed hierarchy.

    features: list[str], every feature name (quotes included if quoted).
    root: str | None, the root feature name.
    feature_hierarchy: dict as produced by BaseFeatureModelBuilder, e.g.
        {parent: {"children": [(child, "mandatory"/"optional"), ...],
                  "groups": [("or"/"xor"/..., [member, ...]), ...]}}.
    constraints: list[str], raw boolean constraint expressions.
    """
    lib = _get_lib()

    edges = []
    groups = []
    for parent, info in feature_hierarchy.items():
        for child, child_type in info["children"]:
            edges.append((parent, child, child_type == "mandatory"))
        for group_type, group_members in info["groups"]:
            if group_type in ("or", "xor"):
                groups.append((parent, group_type, group_members))

    index = {name: i for i, name in enumerate(features)}
    feat_bytes = [name.encode("utf-8") for name in features]
    feat_arr = (ctypes.c_char_p * len(feat_bytes))(*feat_bytes)

    c_edges = (_CEdge * len(edges))(
        *[
            _CEdge(index[parent], index[child], 1 if mandatory else 0)
            for parent, child, mandatory in edges
        ]
    )

    member_indices = []
    c_groups = []
    for parent, kind, members in groups:
        start = len(member_indices)
        member_indices.extend(index[m] for m in members)
        c_groups.append(
            _CGroup(index[parent], 0 if kind == "or" else 1, start, len(members))
        )
    c_groups_arr = (_CGroup * len(c_groups))(*c_groups)
    c_members_arr = (ctypes.c_size_t * len(member_indices))(*member_indices)

    cons_bytes = [c.encode("utf-8") for c in constraints]
    cons_arr = (ctypes.c_char_p * len(cons_bytes))(*cons_bytes)

    root_index = index[root] if root is not None else _NO_ROOT

    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    rc = lib.uvl_hierarchy_to_cnf(
        feat_arr,
        len(feat_bytes),
        root_index,
        c_edges,
        len(c_edges),
        c_groups_arr,
        len(c_groups_arr),
        c_members_arr,
        len(c_members_arr),
        cons_arr,
        len(cons_bytes),
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
    )
    _check(lib, rc)
    return _take_dimacs_buffer(lib, out_ptr, out_len)


def dimacs_to_uvl(dimacs_bytes: bytes, optimize: bool = False, by_name: bool = False) -> str:
    """CNF -> UVL recovery (any2uvl)."""
    lib = _get_lib()
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    rc = lib.uvl_dimacs_to_uvl(
        dimacs_bytes,
        len(dimacs_bytes),
        1 if optimize else 0,
        1 if by_name else 0,
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
    )
    _check(lib, rc)
    try:
        return ctypes.string_at(out_ptr, out_len.value).decode("utf-8")
    finally:
        lib.uvl_free_buffer(out_ptr, out_len)

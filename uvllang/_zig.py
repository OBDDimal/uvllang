"""ctypes bindings for the Zig backend (parser/src/capi.zig).

Entry points:
  - `parse_source_to_cnf`: full pipeline (lex/parse/build/CNF) on raw UVL
    source text, used when Python doesn't parse the file at all.
  - `parse_source_full`: a second, independent lex/parse pass that extracts
    everything Lark/ANTLR's extractor + hierarchy builder do (features,
    types, hierarchy, attributes, raw constraint text) but no CNF -- backs
    UVL's non-CNF properties on backend="zig", called lazily.
  - `hierarchy_to_cnf`: only the CNF-generation step, for a hierarchy and
    constraint list already extracted by Python (ANTLR or Lark).
  - `dimacs_to_uvl`: CNF -> UVL recovery (any2uvl).

`hierarchy_to_cnf` returns `(clauses, id_to_name)`, the shape `UVL.to_cnf`
needs to build a `pysat.formula.CNF`. `parse_source_to_cnf` returns that
plus a third `non_boolean` counts dict (see its docstring). `parse_source_full`
returns a dict, see its docstring. `dimacs_to_uvl` returns UVL text.
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


class _CNonBooleanCounts(ctypes.Structure):
    """Mirrors capi.zig's NonBooleanCounts extern struct exactly (field
    order matters for ctypes layout). Tier 1 fields first, then Tier 2,
    then Tier 3 -- see docs/non_boolean_support.md.
    """

    _fields_ = [
        ("cardinality_groups", ctypes.c_size_t),
        ("constraint_attributes", ctypes.c_size_t),
        ("cardinality_features", ctypes.c_size_t),
        ("attribute_ref_constraints", ctypes.c_size_t),
        ("comparison_constraints", ctypes.c_size_t),
        ("typed_features", ctypes.c_size_t),
        ("attributed_features", ctypes.c_size_t),
    ]

    def as_dict(self):
        return {name: getattr(self, name) for name, _ in self._fields_}


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
        ctypes.POINTER(_CNonBooleanCounts),
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
        ctypes.POINTER(_CNonBooleanCounts),
    ]

    lib.uvl_parse_source_full.restype = ctypes.c_int32
    lib.uvl_parse_source_full.argtypes = [
        ctypes.c_char_p,
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
    """Full pipeline: UVL source text -> (clauses, id_to_name, non_boolean).

    `non_boolean` is a dict of counts for constructs above the plain
    Boolean language level (see docs/non_boolean_support.md) -- Zig has
    already printed its own warnings for each of them to stderr by the
    time this returns; the caller (uvllang.main.UVL) decides whether any
    of them should also raise.
    """
    lib = _get_lib()
    src_bytes = source.encode("utf-8")
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    non_boolean = _CNonBooleanCounts()
    rc = lib.uvl_source_to_cnf(
        src_bytes,
        len(src_bytes),
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
        ctypes.byref(non_boolean),
    )
    _check(lib, rc)
    clauses, id_to_name = _take_dimacs_buffer(lib, out_ptr, out_len)
    return clauses, id_to_name, non_boolean.as_dict()


_NO_INDEX = 0xFFFFFFFF
_GROUP_KIND_NAMES = ("or", "xor", "mandatory_children", "optional_children")


def _read_u32(data, pos):
    return int.from_bytes(data[pos : pos + 4], "little"), pos + 4


def _read_bytes(data, pos):
    n, pos = _read_u32(data, pos)
    return data[pos : pos + n], pos + n


def _decode_parse_source_full(data: bytes) -> dict:
    pos = 0
    n_features, pos = _read_u32(data, pos)
    features = []
    feature_types = {}
    for _ in range(n_features):
        name_b, pos = _read_bytes(data, pos)
        type_b, pos = _read_bytes(data, pos)
        name = name_b.decode("utf-8")
        features.append(name)
        if type_b:
            feature_types[name] = type_b.decode("utf-8")

    root_idx, pos = _read_u32(data, pos)
    root = features[root_idx] if root_idx != _NO_INDEX else None

    feature_hierarchy = {
        name: {"parent": None, "children": [], "groups": []} for name in features
    }

    n_edges, pos = _read_u32(data, pos)
    for _ in range(n_edges):
        parent_idx, pos = _read_u32(data, pos)
        child_idx, pos = _read_u32(data, pos)
        mandatory = data[pos]
        pos += 1
        parent, child = features[parent_idx], features[child_idx]
        feature_hierarchy[parent]["children"].append(
            (child, "mandatory" if mandatory else "optional")
        )
        feature_hierarchy[child]["parent"] = parent

    n_groups, pos = _read_u32(data, pos)
    for _ in range(n_groups):
        parent_idx, pos = _read_u32(data, pos)
        kind = data[pos]
        pos += 1
        member_count, pos = _read_u32(data, pos)
        members = []
        for _ in range(member_count):
            member_idx, pos = _read_u32(data, pos)
            members.append(features[member_idx])
        feature_hierarchy[features[parent_idx]]["groups"].append(
            (_GROUP_KIND_NAMES[kind], members)
        )

    feature_attributes = {}
    n_attrs, pos = _read_u32(data, pos)
    for _ in range(n_attrs):
        feature_idx, pos = _read_u32(data, pos)
        key_b, pos = _read_bytes(data, pos)
        value_b, pos = _read_bytes(data, pos)
        feature_attributes.setdefault(features[feature_idx], {})[
            key_b.decode("utf-8")
        ] = value_b.decode("utf-8")

    raw_constraints = []
    n_constraints, pos = _read_u32(data, pos)
    for _ in range(n_constraints):
        text_b, pos = _read_bytes(data, pos)
        raw_constraints.append(text_b.decode("utf-8"))

    return {
        "features": features,
        "root": root,
        "feature_types": feature_types,
        "feature_hierarchy": feature_hierarchy,
        "feature_attributes": feature_attributes,
        "raw_constraints": raw_constraints,
    }


def parse_source_full(source: str) -> dict:
    """Second full-pipeline entry point: UVL source text -> everything
    Lark/ANTLR's extractor + hierarchy builder produce, minus CNF (see
    `parse_source_to_cnf` for that). Returns:

        {"features": [...],                   # document order
         "root": name-or-None,
         "feature_types": {name: type_str},
         "feature_hierarchy": {name: {"parent": name-or-None,
                                       "children": [(child, "mandatory"/"optional"), ...],
                                       "groups": [(kind_str, [members]), ...]}},
         "feature_attributes": {name: {key: value_str}},   # a bare key with no
                                                            # value (e.g. `abstract`)
                                                            # is omitted, matching
                                                            # Lark/ANTLR
         "raw_constraints": [text, ...]}       # unclassified -- caller splits
                                                # into boolean/arithmetic
    """
    lib = _get_lib()
    src_bytes = source.encode("utf-8")
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    rc = lib.uvl_parse_source_full(
        src_bytes, len(src_bytes), ctypes.byref(out_ptr), ctypes.byref(out_len)
    )
    _check(lib, rc)
    try:
        data = ctypes.string_at(out_ptr, out_len.value)
    finally:
        lib.uvl_free_buffer(out_ptr, out_len)
    return _decode_parse_source_full(data)


def hierarchy_to_cnf(features, root, feature_hierarchy, constraints):
    """Only the CNF-generation step, on an already-parsed hierarchy.

    features: list[str], every feature name (quotes included if quoted).
    root: str | None, the root feature name.
    feature_hierarchy: dict as produced by BaseFeatureModelBuilder, e.g.
        {parent: {"children": [(child, "mandatory"/"optional"), ...],
                  "groups": [("or"/"xor"/..., [member, ...]), ...]}}.
    constraints: list[str], raw boolean constraint expressions -- each is
        re-parsed here with the same real syntactic check
        `parse_source_to_cnf` uses (not a text heuristic), so the returned
        `non_boolean["attribute_ref_constraints"]`/`["comparison_constraints"]`
        are accurate even for a constraint that *looks* boolean-shaped but
        contains a dotted reference with no comparison operator at all
        (e.g. `A.enabled => B`), which Lark/ANTLR's own text-based
        classification can't tell apart from a genuinely boolean one.
        The other five `non_boolean` categories are always 0 here -- this
        function only ever sees an already-extracted hierarchy/constraint
        list, never the raw source those depend on; the caller merges in
        its own tree-walk counts for those.
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
    non_boolean = _CNonBooleanCounts()
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
        ctypes.byref(non_boolean),
    )
    _check(lib, rc)
    clauses, id_to_name = _take_dimacs_buffer(lib, out_ptr, out_len)
    return clauses, id_to_name, non_boolean.as_dict()


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

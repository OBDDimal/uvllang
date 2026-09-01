"""ctypes bindings for the Zig backend (parser/src/capi.zig).

Entry points:
  - `parse_source_to_cnf`: full pipeline (lex/parse/build/CNF) on raw UVL
    source text, used when Python doesn't parse the file at all.
  - `parse_source_full`: a second, independent lex/parse pass that extracts
    everything Lark/ANTLR's extractor + hierarchy builder do (features,
    types, hierarchy, attributes, raw constraint text) but no CNF -- backs
    UVL's non-CNF properties on backend="zig", called lazily.
  - `hierarchy_to_cnf`: only the CNF-generation step, for a hierarchy and
    constraint list already extracted by Python (ANTLR or Lark). Also
    takes `conversion`/`cardinality_groups`, mirroring
    `parse_source_to_cnf`'s `conversion` flag.
  - `is_non_boolean_threatening`: given a `non_boolean` dict, whether
    UVL(drop_non_boolean=False) should raise -- the single source of
    truth for this is capi.zig's NonBooleanCounts.isThreatening.
  - `dimacs_to_uvl`: CNF -> UVL recovery (any2uvl).

`hierarchy_to_cnf` and `parse_source_to_cnf` both return `(non_boolean,
raw_dimacs)` -- `raw_dimacs` is zig's own DIMACS bytes verbatim
(writeDimacs, parser/src/cnf.zig); this module does not parse DIMACS
itself, `UVL.to_cnf`/`UVL.to_dimacs` hand the bytes straight to
`pysat.formula.CNF`. `parse_source_full` returns a dict, see its
docstring. `dimacs_to_uvl` returns `(uvl_text, verify_result)`, see its
docstring.
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


_NO_MAX = 0xFFFFFFFF  # capi.zig's `no_max` sentinel for `[min..*]`


class _CCardinalityGroup(ctypes.Structure):
    _fields_ = [
        ("parent_idx", ctypes.c_size_t),
        ("min", ctypes.c_uint32),
        ("max", ctypes.c_uint32),
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
        ctypes.c_uint8,
        ctypes.c_uint8,
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
        ctypes.POINTER(_CCardinalityGroup),
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_size_t),
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_char_p),
        ctypes.c_size_t,
        ctypes.c_uint8,
        ctypes.c_uint8,
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

    lib.uvl_source_to_smt.restype = ctypes.c_int32
    lib.uvl_source_to_smt.argtypes = [
        ctypes.c_char_p,
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_size_t),
    ]

    lib.uvl_is_non_boolean_threatening.restype = ctypes.c_uint8
    lib.uvl_is_non_boolean_threatening.argtypes = [
        ctypes.POINTER(_CNonBooleanCounts),
        ctypes.c_uint8,
    ]

    lib.uvl_dimacs_to_uvl.restype = ctypes.c_int32
    lib.uvl_dimacs_to_uvl.argtypes = [
        ctypes.c_char_p,
        ctypes.c_size_t,
        ctypes.c_uint8,
        ctypes.c_uint8,
        ctypes.c_uint8,
        ctypes.c_uint8,
        ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_size_t),
        ctypes.POINTER(ctypes.c_size_t),
        ctypes.POINTER(ctypes.c_size_t),
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


def _take_buffer(lib, out_ptr, out_len):
    try:
        return ctypes.string_at(out_ptr, out_len.value)
    finally:
        lib.uvl_free_buffer(out_ptr, out_len)


def parse_source_to_cnf(source: str, simplify: bool = False, conversion: bool = False):
    """Full pipeline: UVL source text -> (non_boolean, raw_dimacs).

    `raw_dimacs` is zig's own DIMACS bytes (writeDimacs, parser/src/cnf.zig)
    -- the same bytes `uvl2cnf` writes -- for the caller (uvllang.uvl.UVL)
    to hand to `pysat.formula.CNF(from_string=...)` directly; this module
    does not parse DIMACS itself.

    `non_boolean` is a dict of counts for constructs above the plain
    Boolean language level (see docs/non_boolean_support.md) -- Zig has
    already printed its own warnings for each of them to stderr by the
    time this returns; the caller decides whether any of them should also
    raise.

    `simplify` gates the global subsumption/SSR-disabled clause-set
    simplification pass (see docs/pipeline_clause_dedup.md) -- off by
    default, matching the `uvl2cnf` CLI's `--simplify` flag, so this API
    and the CLI produce the same clause set for the same input unless the
    caller explicitly opts in.

    `conversion` gates the UVLParser-paper conversion strategies for group
    cardinality and feature-local constraint attributes (see
    parser/src/conversion.zig / docs/non_boolean_support.md) -- off by
    default, matching the `uvl2cnf` CLI's `--conversion` flag.
    """
    lib = _get_lib()
    src_bytes = source.encode("utf-8")
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    non_boolean = _CNonBooleanCounts()
    rc = lib.uvl_source_to_cnf(
        src_bytes,
        len(src_bytes),
        1 if simplify else 0,
        1 if conversion else 0,
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
        ctypes.byref(non_boolean),
    )
    _check(lib, rc)
    raw_dimacs = _take_buffer(lib, out_ptr, out_len)
    return non_boolean.as_dict(), raw_dimacs


def is_non_boolean_threatening(non_boolean: dict, conversion: bool = False) -> bool:
    """True iff `non_boolean` (a dict as returned by parse_source_to_cnf/
    hierarchy_to_cnf, merged with a caller's own tree-walk counts where
    applicable) should make to_cnf()/to_dimacs() raise instead of
    silently continuing. Single source of truth: capi.zig's
    NonBooleanCounts.isThreatening (parser/src/pipeline.zig), shared with
    the `uvl2cnf --strict` CLI flag.
    """
    lib = _get_lib()
    counts = _CNonBooleanCounts(**non_boolean)
    return bool(
        lib.uvl_is_non_boolean_threatening(ctypes.byref(counts), 1 if conversion else 0)
    )


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

    boolean_constraints = []
    arithmetic_constraints = []
    n_constraints, pos = _read_u32(data, pos)
    for _ in range(n_constraints):
        text_b, pos = _read_bytes(data, pos)
        is_boolean = data[pos]
        pos += 1
        text = text_b.decode("utf-8")
        (boolean_constraints if is_boolean else arithmetic_constraints).append(text)

    return {
        "features": features,
        "root": root,
        "feature_types": feature_types,
        "feature_hierarchy": feature_hierarchy,
        "feature_attributes": feature_attributes,
        "boolean_constraints": boolean_constraints,
        "arithmetic_constraints": arithmetic_constraints,
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
         "boolean_constraints": [text, ...],    # already classified by
         "arithmetic_constraints": [text, ...]} # constraint.zig itself
                                                 # (c.node != null), not a
                                                 # Python-side text guess
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


def write_bytes(data: bytes, filepath) -> None:
    with open(filepath, "wb") as f:
        f.write(data)


def source_to_smt(source: str, filepath=None):
    """Full pipeline: UVL source text -> SMT-LIB 2, via the native writer
    (parser/src/smt.zig). Unlike parse_source_to_cnf, not restricted to
    the plain Boolean language level -- numeric comparisons, aggregates,
    and typed features are all represented. Backs UVL.to_smt() for
    backend="zig"; the native uvl2smt binary calls the same Zig code
    directly, without going through Python at all.

    Returns the text if `filepath` is None; otherwise writes zig's own
    bytes to `filepath` verbatim (no decode/re-encode round trip) and
    returns None.
    """
    lib = _get_lib()
    src_bytes = source.encode("utf-8")
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    rc = lib.uvl_source_to_smt(
        src_bytes, len(src_bytes), ctypes.byref(out_ptr), ctypes.byref(out_len)
    )
    _check(lib, rc)
    raw = _take_buffer(lib, out_ptr, out_len)
    if filepath is None:
        return raw.decode("utf-8")
    write_bytes(raw, filepath)
    return None


def hierarchy_to_cnf(
    features,
    root,
    feature_hierarchy,
    constraints,
    simplify: bool = False,
    conversion: bool = False,
    cardinality_groups=None,
):
    """Only the CNF-generation step, on an already-parsed hierarchy.
    Returns (non_boolean, raw_dimacs) -- see parse_source_to_cnf's
    docstring.

    features: list[str], every feature name (quotes included if quoted).
    root: str | None, the root feature name.
    simplify: see parse_source_to_cnf -- off by default, same semantics.
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
    conversion: mirrors parse_source_to_cnf's `conversion` flag -- applies
        the group-cardinality encoding (parser/src/conversion.zig) to
        `cardinality_groups`. Feature-local constraint attributes need no
        separate parameter: fold their text into `constraints` before
        calling this, the same as any other constraint.
    cardinality_groups: list[(parent, min, max_or_None, [member, ...])],
        as produced by BaseFeatureModelBuilder.cardinality_groups. Ignored
        unless conversion=True.
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

    cg_member_indices = []
    c_cardinality_groups = []
    for parent, min_, max_, members in cardinality_groups or []:
        start = len(cg_member_indices)
        cg_member_indices.extend(index[m] for m in members)
        c_cardinality_groups.append(
            _CCardinalityGroup(
                index[parent],
                min_,
                _NO_MAX if max_ is None else max_,
                start,
                len(members),
            )
        )
    c_cardinality_groups_arr = (_CCardinalityGroup * len(c_cardinality_groups))(
        *c_cardinality_groups
    )
    c_cg_members_arr = (ctypes.c_size_t * len(cg_member_indices))(*cg_member_indices)

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
        c_cardinality_groups_arr,
        len(c_cardinality_groups_arr),
        c_cg_members_arr,
        len(c_cg_members_arr),
        cons_arr,
        len(cons_bytes),
        1 if simplify else 0,
        1 if conversion else 0,
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
        ctypes.byref(non_boolean),
    )
    _check(lib, rc)
    raw_dimacs = _take_buffer(lib, out_ptr, out_len)
    return non_boolean.as_dict(), raw_dimacs


def dimacs_to_uvl(
    dimacs_bytes: bytes,
    optimize: bool = False,
    by_name: bool = False,
    infer_propagation: bool = False,
    verify: bool = False,
):
    """CNF -> UVL recovery (any2uvl). `infer_propagation` enables the
    experimental, opt-in propagation-based (unit-propagation/BCP)
    implication recovery pass -- see recovery.zig's
    `augmentGraphWithPropagation` doc comment. Off by default: it's more
    expensive than the default literal-clause-shape matching and is meant
    to be benchmarked before ever being turned on by default.

    `verify` re-parses the recovered text and compares its CNF against
    the input as an exact clause set, entirely in Zig
    (recovery.verifyRecovery) -- the same check `any2uvl --verify` runs.

    Returns `(uvl_text, verify_result)`; `verify_result` is `None` unless
    `verify=True`, else a dict with `total_orig_clauses`/`missing`/`extra`.
    """
    lib = _get_lib()
    out_ptr = ctypes.c_void_p()
    out_len = ctypes.c_size_t()
    orig_clauses = ctypes.c_size_t()
    missing = ctypes.c_size_t()
    extra = ctypes.c_size_t()
    rc = lib.uvl_dimacs_to_uvl(
        dimacs_bytes,
        len(dimacs_bytes),
        1 if optimize else 0,
        1 if by_name else 0,
        1 if infer_propagation else 0,
        1 if verify else 0,
        ctypes.byref(out_ptr),
        ctypes.byref(out_len),
        ctypes.byref(orig_clauses),
        ctypes.byref(missing),
        ctypes.byref(extra),
    )
    _check(lib, rc)
    verify_result = (
        {
            "total_orig_clauses": orig_clauses.value,
            "missing": missing.value,
            "extra": extra.value,
        }
        if verify
        else None
    )
    try:
        return ctypes.string_at(out_ptr, out_len.value).decode("utf-8"), verify_result
    finally:
        lib.uvl_free_buffer(out_ptr, out_len)

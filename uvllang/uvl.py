import os

from pysat.formula import CNF

from uvllang import _zig


class NonBooleanConstructError(ValueError):
    """Raised by to_cnf() for constructs above the Boolean language level
    (README.md#non-boolean-constructs). drop_non_boolean=True warns instead.
    """


class _ZigBuilder:
    """UVL.builder()'s return value for backend="zig": exposes
    .root_feature/.feature_hierarchy.
    """

    def __init__(self, root_feature, feature_hierarchy):
        self.root_feature = root_feature
        self.feature_hierarchy = feature_hierarchy


def _backend_module(name):
    """Imports uvllang.antlr4.uvl_antlr_parser / uvllang.lark.uvl_lark_parser
    on first actual use of that backend -- a plain top-level `import`
    would defeat the point of `_lark`/`_antlr`'s own lazy loading inside
    those modules, since the antlr4/lark packages would then always be
    imported (if not the antlr4/lark libraries themselves) regardless of
    which backend is requested.
    """
    if name == "antlr":
        from uvllang.antlr4 import uvl_antlr_parser

        return uvl_antlr_parser
    from uvllang.lark import uvl_lark_parser

    return uvl_lark_parser


class UVL:
    """
    backend: "zig" (default), "lark", or "antlr".

    "zig" runs the whole pipeline natively. `.tree` returns each
    backend's own shape: a Lark Tree, an ANTLR ParserRuleContext, or
    (backend="zig") the flat dict from uvllang._zig.parse_source_full.

    Exactly one of from_file (a .uvl path), from_str (UVL source text), or
    from_cnf must be given. from_cnf recovers a UVL model from a CNF
    (any2uvl, entirely in Zig) -- either a DIMACS file path, or a
    pysat.formula.CNF-like object (anything with .to_dimacs()). The
    recovered UVL text is then parsed like from_str, on whichever backend
    was requested. optimize/by_name are recovery-quality knobs, only
    meaningful with from_cnf (see uvllang._zig.dimacs_to_uvl).

    to_cnf()/to_dimacs() support only the Boolean language level
    (README.md#non-boolean-constructs) and raise NonBooleanConstructError if
    the model has group cardinality, feature-local constraint attributes,
    or feature cardinality; drop_non_boolean=True warns instead. to_smt()
    has no such restriction.

    conversion=True converts group cardinality and feature-local
    constraint attributes instead of dropping them (UVLParser paper,
    Sundermann et al., SPLC'23), on every backend; feature cardinality is
    still dropped.

    simplify=True additionally runs the global subsumption/SSR pass
    (README.md#cnf-clause-set-simplification).
    """

    def __init__(
        self,
        from_file=None,
        from_str=None,
        from_cnf=None,
        use_antlr=False,
        backend=None,
        drop_non_boolean=False,
        simplify=False,
        conversion=False,
        optimize=False,
        by_name=False,
    ):
        sources = [s for s in (from_file, from_str, from_cnf) if s is not None]
        if len(sources) != 1:
            raise ValueError(
                "Exactly one of from_file, from_str, or from_cnf is required"
            )

        if from_cnf is not None:
            if isinstance(from_cnf, (str, os.PathLike)):
                with open(from_cnf, "rb") as f:
                    dimacs_bytes = f.read()
            else:
                dimacs_bytes = from_cnf.to_dimacs().encode("utf-8")
            from_str = _zig.dimacs_to_uvl(
                dimacs_bytes,
                optimize=optimize,
                by_name=by_name,
            )
        elif optimize or by_name:
            raise ValueError("optimize/by_name only apply to from_cnf")

        if backend is None:
            backend = "antlr" if use_antlr else "zig"
        if backend not in ("zig", "lark", "antlr"):
            raise ValueError(
                f"backend must be one of 'zig', 'lark', 'antlr', got {backend!r}"
            )

        self._parser_module = None
        if backend in ("antlr", "lark"):
            # Fail fast before parsing.
            self._parser_module = _backend_module(backend)
            self._parser_module.load()

        self._backend = backend
        self._drop_non_boolean = drop_non_boolean
        self._simplify = simplify
        self._conversion = conversion
        self._file_path = from_file
        self._content = from_str
        self._tree = None
        self._extractor = None
        self._builder = None
        self._zig_dimacs = None
        self._non_boolean = None
        self._source = None
        self._zig_full = None
        self._parse()

    def _ensure_zig_full(self):
        """Lazily runs uvllang._zig.parse_source_full, caching the result."""
        if self._zig_full is None:
            self._zig_full = _zig.parse_source_full(self._source)
        return self._zig_full

    def _read_content(self):
        if self._file_path:
            with open(self._file_path, "r", encoding="utf-8") as f:
                return f.read()
        return self._content

    def _check_non_boolean(self):
        """Raises NonBooleanConstructError unless drop_non_boolean was
        passed. Which categories are threatening, and how conversion=True
        exempts two of them, is decided once by
        uvllang._zig.is_non_boolean_threatening (capi.zig's
        NonBooleanCounts.isThreatening) -- not tracked here.
        """
        if self._drop_non_boolean:
            return
        if _zig.is_non_boolean_threatening(self._non_boolean, self._conversion):
            found = ", ".join(f"{c}={n}" for c, n in self._non_boolean.items() if n)
            raise NonBooleanConstructError(
                f"model uses constructs above the Boolean language level "
                f"that would be silently dropped: {found}. Pass "
                "drop_non_boolean=True to warn and continue instead."
            )

    def _parse(self):
        self._source = self._read_content()

        if self._backend == "zig":
            self._non_boolean, self._zig_dimacs = _zig.parse_source_to_cnf(
                self._source, simplify=self._simplify, conversion=self._conversion
            )
            return

        self._tree, self._extractor, self._builder = self._parser_module.parse(
            self._source
        )

        features = sorted(set(self._extractor.features))
        root = self._builder.root_feature or None
        # self.constraints, not just self.boolean_constraints:
        # hierarchy_to_cnf re-derives Boolean/arithmetic status itself.
        constraints = self.constraints
        if self._conversion:
            # A feature-local constraint attribute is just another
            # constraint that must hold -- hierarchy_to_cnf's constraint
            # loop already classifies/converts each entry identically, so
            # no separate parameter is needed for these.
            constraints = constraints + self._extractor.feature_local_constraint_texts
        self._non_boolean, self._zig_dimacs = _zig.hierarchy_to_cnf(
            features,
            root,
            self._builder.feature_hierarchy,
            constraints,
            simplify=self._simplify,
            conversion=self._conversion,
            cardinality_groups=self._builder.cardinality_groups,
        )
        self._non_boolean.update(
            cardinality_groups=self._builder.cardinality_group_count,
            constraint_attributes=self._extractor.constraint_attribute_count,
            cardinality_features=self._extractor.cardinality_feature_count,
            typed_features=len(self._extractor.feature_types),
            attributed_features=len(self._extractor.feature_attributes),
        )

    @property
    def tree(self):
        """The backend's own parse tree: a Lark Tree, an ANTLR
        ParserRuleContext, or (backend="zig") the flat parsed-model dict
        from uvllang._zig.parse_source_full -- zig's AST itself isn't
        marshalled across the C ABI, only this already-flattened data,
        which every other property on this class is already built from.
        """
        if self._backend == "zig":
            return self._ensure_zig_full()
        return self._tree

    @property
    def features(self):
        """All feature names, in document order."""
        if self._backend == "zig":
            return self._ensure_zig_full()["features"]
        return self._extractor.features

    @property
    def constraints(self):
        return self.boolean_constraints + self.arithmetic_constraints

    @property
    def boolean_constraints(self):
        """Boolean constraints convertible to CNF."""
        if self._backend == "zig":
            return self._ensure_zig_full()["boolean_constraints"]
        return self._extractor.boolean_constraints

    @property
    def arithmetic_constraints(self):
        """Arithmetic constraints not convertible to CNF."""
        if self._backend == "zig":
            return self._ensure_zig_full()["arithmetic_constraints"]
        return self._extractor.arithmetic_constraints

    @property
    def feature_types(self):
        """Feature type annotations."""
        if self._backend == "zig":
            return self._ensure_zig_full()["feature_types"]
        return self._extractor.feature_types

    @property
    def feature_attributes(self):
        """Feature attributes with their values."""
        if self._backend == "zig":
            return self._ensure_zig_full()["feature_attributes"]
        return self._extractor.feature_attributes

    def builder(self):
        """Feature hierarchy builder."""
        if self._backend == "zig":
            full = self._ensure_zig_full()
            return _ZigBuilder(full["root"], full["feature_hierarchy"])
        return self._builder

    def to_cnf(self, verbose_info=True):
        """Parses zig's own DIMACS output (self._zig_dimacs, parser/src/
        cnf/cnf.zig's writeDimacs) with pysat.formula.CNF directly -- ids
        are always zig's own (alphabetical by feature name), never
        caller-chosen. Raises NonBooleanConstructError unless
        drop_non_boolean was passed to the constructor.

        verbose_info: accepted, unused.
        """
        self._check_non_boolean()
        return CNF(from_string=self._zig_dimacs.decode("utf-8"))

    def to_dimacs(self, filepath):
        """Writes zig's own DIMACS output (self._zig_dimacs) to `filepath`
        verbatim -- the same bytes `uvl2cnf` writes.
        """
        self._check_non_boolean()
        _zig.write_bytes(self._zig_dimacs, filepath)

    def to_smt(self, filepath=None):
        """Convert feature model to SMT-LIB 2 format via
        uvllang._zig.source_to_smt (parser/src/smt/writer.zig), for all backends.
        Returns the text if `filepath` is None, else writes zig's own
        bytes there directly and returns None.
        """
        return _zig.source_to_smt(self._source, filepath)

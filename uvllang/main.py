import re
import os

from pysat.formula import CNF

from uvllang import _zig
from uvllang.uvl_lark_lexer import UVLIndentationLexer

# Lark itself (parser construction, grammar loading, the earley engine) is
# ~28ms of import time -- real cost on tiny models where actual parsing is
# sub-millisecond. Only backend="lark" needs it, so it's loaded on first use
# rather than unconditionally for every UVL/CLI invocation.
_lark_mod = None


def _lark():
    global _lark_mod, Tree, Token, Lark
    if _lark_mod is None:
        import lark as _lark_mod_
        _lark_mod = _lark_mod_
        Tree, Token, Lark = _lark_mod.Tree, _lark_mod.Token, _lark_mod.Lark
    return _lark_mod

try:
    from antlr4 import CommonTokenStream, FileStream, InputStream
    from uvllang.uvl_custom_lexer import uvl_custom_lexer
    from uvllang.uvl_python_parser import uvl_python_parser
    from uvllang.uvl_python_parser_listener import uvl_python_parserListener
    from antlr4.error.ErrorListener import ErrorListener
    from antlr4.tree.Tree import ParseTreeWalker

    ANTLR_AVAILABLE = True

    class CustomErrorListener(ErrorListener):
        def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
            if "\\t" in msg:
                print(f"Warning: Line {line}:{column} - {msg}")
                return
            raise Exception(f"Parse error at line {line}:{column} - {msg}")

except ImportError:
    ANTLR_AVAILABLE = False
    uvl_python_parserListener = object


# Tier 1/2 categories from uvllang._zig.parse_source_to_cnf's non_boolean
# dict -- the ones NonBooleanConstructError raises on by default (see
# docs/non_boolean_support.md). Tier 3 (typed_features, attributed_features)
# is deliberately excluded: decorative metadata, never raises.
_THREATENING_NON_BOOLEAN_CATEGORIES = (
    "cardinality_groups",
    "constraint_attributes",
    "cardinality_features",
    "attribute_ref_constraints",
    "comparison_constraints",
)


class NonBooleanConstructError(ValueError):
    """Raised by UVL(backend="zig") when the model uses a construct above
    the plain Boolean language level whose absence would threaten the
    CNF's semantics -- see docs/non_boolean_support.md. Pass
    drop_non_boolean=True to warn and continue instead (matching the
    uvl2cnf CLI's behavior, which always warns and never raises).
    """


class UVL:
    """
    backend: "zig" (default), "lark", or "antlr".

    "zig" runs the whole pipeline (lex, parse, hierarchy, CNF) in the Zig
    backend (uvllang._zig) and is the fastest option. It supports everything
    Lark/ANTLR do -- `.features`, `.feature_types`, `.feature_attributes`,
    `.boolean_constraints`, `.arithmetic_constraints`, `.builder()`,
    `to_smt()` -- except `.tree`: Lark and ANTLR already produce two
    unrelated tree shapes (different grammars/tools), so there was never a
    shared concept there to extend to zig; it raises NotImplementedError on
    every backend but the one that parsed it.

    The non-CNF properties above run a second, independent lex/parse pass
    (uvllang._zig.parse_source_full) the first time any of them is
    accessed, cached after that. to_cnf() never triggers it -- it's built
    entirely from the single fast pass __init__ already did.

    Only the plain Boolean language level is supported for CNF conversion
    (see docs/non_boolean_support.md), identically across all three
    backends. Group cardinality ([i..j] groups), feature-local
    `{constraint ...}` attributes, and feature cardinality (clone
    multiplicity) all silently threaten the resulting CNF's semantics if
    ignored, so to_cnf() raises NonBooleanConstructError by default when
    any of them is present, on every backend -- not the constructor itself,
    since this limitation is specific to CNF conversion (to_smt() has no
    such restriction). Pass drop_non_boolean=True to the constructor to
    warn (a warning is always printed either way, from parsing onward) and
    continue instead. Typed features and inert value attributes are
    always just warned about, never raised on, since they don't affect the
    Boolean skeleton's correctness and are common in real models.
    """

    def __init__(
        self,
        from_file=None,
        from_str=None,
        use_antlr=False,
        backend=None,
        drop_non_boolean=False,
    ):
        # Exactly one of from_file or from_str must be specified
        if from_file is None and from_str is None:
            raise ValueError("Either from_file or from_str parameter is required")
        if from_file is not None and from_str is not None:
            raise ValueError("Cannot specify both from_file and from_str parameters")

        if backend is None:
            backend = "antlr" if use_antlr else "zig"
        if backend not in ("zig", "lark", "antlr"):
            raise ValueError(
                f"backend must be one of 'zig', 'lark', 'antlr', got {backend!r}"
            )

        if backend == "antlr" and not ANTLR_AVAILABLE:
            raise ImportError(
                "ANTLR parser requested but ANTLR dependencies not available. "
                "Install with: pip install uvllang[antlr]"
            )

        self._backend = backend
        self._use_antlr = backend == "antlr"
        self._drop_non_boolean = drop_non_boolean
        self._file_path = from_file
        self._content = from_str
        self._tree = None
        self._extractor = None
        self._builder = None
        self._zig_clauses = None
        self._zig_id_to_name = None
        self._non_boolean = None
        self._source = None
        self._zig_full = None
        self._parse()

    def _not_available_on_zig_backend(self, attr_name):
        raise NotImplementedError(
            f"'{attr_name}' is not available on backend={self._backend!r} -- "
            "it's backend-specific (Lark/ANTLR already produce two unrelated "
            "tree shapes; there's no shared concept to extend to zig)."
        )

    def _ensure_zig_full(self):
        """Lazily runs uvllang._zig.parse_source_full, caching the result.
        Only backend="zig" properties besides to_cnf()/.features call this
        -- to_cnf() is built entirely from __init__'s existing fast pass.
        """
        if self._zig_full is None:
            full = _zig.parse_source_full(self._source)
            full["boolean_constraints"] = []
            full["arithmetic_constraints"] = []
            for text in full["raw_constraints"]:
                if _is_arithmetic_constraint(text):
                    full["arithmetic_constraints"].append(text)
                else:
                    full["boolean_constraints"].append(text)
            self._zig_full = full
        return self._zig_full

    @classmethod
    def from_cnf(cls, filepath, file_out, optimize=False, by_name=False, verify=False):
        """CNF -> UVL recovery (any2uvl). The algorithm runs entirely in the
        Zig backend (uvllang._zig.dimacs_to_uvl); this handles file I/O and
        the optional --verify round-trip check.
        """
        with open(filepath, "rb") as f:
            dimacs_bytes = f.read()

        uvl_text = _zig.dimacs_to_uvl(dimacs_bytes, optimize=optimize, by_name=by_name)

        with open(file_out, "w", encoding="utf-8") as f:
            f.write(uvl_text)

        if verify:
            orig_set = {
                tuple(sorted(c, key=abs)) for c in CNF(from_file=filepath).clauses
            }
            result_clauses, _, _ = _zig.parse_source_to_cnf(uvl_text)
            result_set = {tuple(sorted(c, key=abs)) for c in result_clauses}
            missing = orig_set - result_set
            extra = result_set - orig_set
            if missing or extra:
                print(
                    f"from_cnf: DIMACS check FAIL: missing={len(missing)} extra={len(extra)}"
                )
            else:
                print(f"from_cnf: DIMACS PASS ({len(orig_set)} clauses)")

    def _read_content(self):
        if self._file_path:
            with open(self._file_path, "r", encoding="utf-8") as f:
                return f.read()
        return self._content

    def _check_non_boolean(self):
        """Raises NonBooleanConstructError if any Tier 1/2 count is nonzero
        and drop_non_boolean wasn't passed -- see docs/non_boolean_support.md.
        Called from to_cnf(), not __init__: the Boolean-only limitation is
        specific to CNF conversion (to_smt() has no such restriction --
        SMT-LIB can represent arithmetic constraints and typed features
        just fine), so parsing a model that merely *uses* one of these
        constructs shouldn't fail before anyone's actually asked for a CNF.
        __init__ still always computes the CNF eagerly for all three
        backends (uvllang._zig already printed its own warnings to stderr
        by that point regardless) -- only the raise itself is deferred.
        """
        if self._drop_non_boolean:
            return
        threatened = {
            category: count
            for category in _THREATENING_NON_BOOLEAN_CATEGORIES
            if (count := self._non_boolean.get(category, 0)) > 0
        }
        if threatened:
            found = ", ".join(f"{c}={n}" for c, n in threatened.items())
            raise NonBooleanConstructError(
                f"model uses constructs above the Boolean language level "
                f"that would be silently dropped: {found}. Pass "
                "drop_non_boolean=True to warn and continue instead."
            )

    def _parse(self):
        if self._backend == "zig":
            self._source = self._read_content()
            self._zig_clauses, self._zig_id_to_name, self._non_boolean = _zig.parse_source_to_cnf(
                self._source
            )
            return

        if self._use_antlr:
            if self._file_path:
                input_stream = FileStream(self._file_path)
            else:
                input_stream = InputStream(self._content)


            lexer = uvl_custom_lexer(input_stream)
            lexer.removeErrorListeners()
            lexer.addErrorListener(CustomErrorListener())

            stream = CommonTokenStream(lexer)
            parser = uvl_python_parser(stream)
            parser.removeErrorListeners()
            parser.addErrorListener(CustomErrorListener())

            self._tree = parser.featureModel()

            self._extractor = AntlrFeatureExtractor()
            self._builder = AntlrFeatureModelBuilder()
            walker = ParseTreeWalker()
            walker.walk(self._extractor, self._tree)
            walker.walk(self._builder, self._tree)

        else:
            _lark()
            content = self._read_content()

            lexer = UVLIndentationLexer()
            processed_content = lexer.process(content)

            parser = _load_lark_parser()
            self._tree = parser.parse(processed_content)

            self._extractor = LarkFeatureExtractor()
            self._builder = LarkFeatureModelBuilder()
            self._extractor.visit(self._tree)
            self._builder.visit(self._tree)

        # CNF generation, eagerly, for lark/antlr too: matches backend="zig"
        # (which also runs its equivalent, uvl_source_to_cnf, in __init__),
        # so to_cnf() below is a single shared fast path for all three --
        # no per-backend branching left, and non_boolean is populated
        # identically for the to_cnf()-time NonBooleanConstructError check.
        # The `features` list's order is irrelevant to the result: Zig's
        # own id assignment (cnf.zig:assignIds) always sorts alphabetically
        # regardless of what order names are passed in.
        features = sorted(set(self._extractor.features))
        root = self._builder.root_feature or None
        # All constraints, not just self.boolean_constraints: the
        # heuristic text-based split (_is_arithmetic_constraint) can
        # misclassify a boolean-shaped constraint with a dotted reference
        # and no comparison operator at all (e.g. `A.enabled => B`) as
        # boolean -- passing only that subset would silently exclude the
        # genuinely-arithmetic ones from hierarchy_to_cnf's real
        # per-constraint check entirely, undercounting comparison_constraints.
        # hierarchy_to_cnf re-derives real node/skip status for every one
        # of them regardless, so this changes nothing about which clauses
        # get generated, only which get correctly counted.
        self._zig_clauses, self._zig_id_to_name, self._non_boolean = _zig.hierarchy_to_cnf(
            features, root, self._builder.feature_hierarchy, self.constraints
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
        if self._backend == "zig":
            self._not_available_on_zig_backend("tree")
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

    def to_cnf(self, features2ids=None, verbose_info=True):
        """CNF generation runs in the Zig backend (uvllang._zig).

        The whole pipeline -- lex/parse (backend-specific), hierarchy, and
        CNF -- already ran once during __init__ for all three backends
        (uvllang._zig.parse_source_to_cnf for zig,
        uvllang._zig.hierarchy_to_cnf for lark/antlr), so this is always
        just a remap onto features2ids, identical across backends.

        Raises NonBooleanConstructError if the model uses a Tier 1/2
        construct (see docs/non_boolean_support.md) unless drop_non_boolean
        was passed to the constructor.

        verbose_info is accepted for backward compatibility but unused:
        Zig already prints its own ignored-constraint/non-Boolean warnings
        unconditionally during __init__ regardless of this flag (matching
        the "always warn" policy in docs/non_boolean_support.md).
        """
        self._check_non_boolean()
        if features2ids is None:
            # Zig's own id assignment (cnf.zig: assignIds) already sorts
            # feature names the same way this default does, so the ids
            # it returned during __init__ already match -- skip the
            # per-literal remap below, which is the dominant cost on
            # large models (350k+ clauses).
            cnf = CNF(from_clauses=self._zig_clauses)
            cnf.comments = [
                f"c {feature_id} {feature_name}"
                for feature_id, feature_name in sorted(self._zig_id_to_name.items())
            ]
            # CNF(from_clauses=...) infers nv from the highest variable
            # index actually appearing in a clause, not the true feature
            # count -- a feature subsumption elimination leaves totally
            # unconstrained (no surviving clause mentions it at all) would
            # silently undercount nv, producing a DIMACS header
            # inconsistent with its own comments.
            cnf.nv = max(cnf.nv, len(self._zig_id_to_name))
            return cnf
        clauses = [
            [
                (
                    features2ids[self._zig_id_to_name[lit]]
                    if lit > 0
                    else -features2ids[self._zig_id_to_name[-lit]]
                )
                for lit in clause
            ]
            for clause in self._zig_clauses
        ]
        cnf = CNF(from_clauses=clauses)
        cnf.comments = [
            f"c {feature_id} {feature_name}"
            for feature_name, feature_id in features2ids.items()
        ]
        # See the from_clauses branch above: nv must cover every declared
        # feature, not just ones a surviving clause happens to mention.
        cnf.nv = max(cnf.nv, len(features2ids))
        return cnf

    def to_smt(self):
        """Convert feature model to SMT-LIB 2 format."""
        builder = self.builder()
        lines = []

        # Collect string-typed features
        string_features = set()
        for feature in self.features:
            if (
                feature in self.feature_types and "String" in self.feature_types[feature]
            ):
                string_features.add(feature)

        # Declare boolean variables for features
        lines.append("; Feature declarations")
        for feature in self.features:
            lines.append(f"(declare-const {feature} Bool)")

        # Declare string variables for String-typed features
        if string_features:
            lines.append("")
            lines.append("; String feature values")
            for feature in sorted(string_features):
                lines.append(f"(declare-const {feature}_val String)")

        # Declare integer/real variables for attributes
        lines.append("")
        lines.append("; Attribute declarations")
        attribute_vars = set()

        # Collect attributes from arithmetic constraints
        for constraint in self.arithmetic_constraints:
            expanded = self._expand_aggregates(constraint)
            # Extract attribute references (e.g., B.Price, C.Fun)

            attrs = re.findall(r"([A-Za-z_]\w*\.[A-Za-z_]\w*)", expanded)
            attribute_vars.update(attrs)

        # Also collect all attributes from feature declarations
        for feature, attrs in self.feature_attributes.items():
            for attr_name in attrs.keys():
                attribute_vars.add(f"{feature}.{attr_name}")

        for attr in sorted(attribute_vars):
            lines.append(f"(declare-const {attr} Int)")

        # Attribute value constraints from feature declarations
        if self.feature_attributes:
            lines.append("")
            lines.append("; Attribute value constraints")
            for feature, attrs in sorted(self.feature_attributes.items()):
                for attr_name, attr_value in sorted(attrs.items()):
                    attr_ref = f"{feature}.{attr_name}"
                    lines.append(f"(assert (= {attr_ref} {attr_value}))")

        # Root feature constraint
        lines.append("")
        lines.append("; Root feature must be selected")
        if builder.root_feature:
            lines.append(f"(assert {builder.root_feature})")

        # Hierarchy constraints
        lines.append("")
        lines.append("; Hierarchy constraints")
        for feature, info in builder.feature_hierarchy.items():
            for child, child_type in info["children"]:
                # Child implies parent
                lines.append(f"(assert (=> {child} {feature}))")
                # Mandatory: parent implies child
                if child_type == "mandatory":
                    lines.append(f"(assert (=> {feature} {child}))")

            for group_type, group_members in info["groups"]:
                if group_type == "or":
                    # Parent implies at least one child
                    or_clause = " ".join(group_members)
                    lines.append(f"(assert (=> {feature} (or {or_clause})))")

                elif group_type == "xor":
                    # Parent implies exactly one child
                    or_clause = " ".join(group_members)
                    lines.append(f"(assert (=> {feature} (or {or_clause})))")
                    # At most one (mutual exclusion)
                    for i, m1 in enumerate(group_members):
                        for m2 in group_members[i + 1 :]:
                            lines.append(f"(assert (not (and {m1} {m2})))")

        # Boolean constraints
        if self.boolean_constraints:
            lines.append("")
            lines.append("; Boolean constraints")
            for constraint in self.boolean_constraints:
                smt_constraint = self._boolean_to_smt(constraint)
                lines.append(f"(assert {smt_constraint})")

        # Arithmetic constraints
        if self.arithmetic_constraints:
            lines.append("")
            lines.append("; Arithmetic constraints")
            for constraint in self.arithmetic_constraints:
                smt_constraint = self._arithmetic_to_smt(constraint)
                lines.append(f"(assert {smt_constraint})")

        lines.append("")
        lines.append("(check-sat)")
        lines.append("(get-model)")

        return "\n".join(lines)

    def _boolean_to_smt(self, constraint):
        """Convert boolean constraint to SMT-LIB format."""
        
        def parse_boolean_expr(expr):
            """Recursively parse and convert boolean expression to SMT-LIB."""
            expr = expr.strip()
            
            # Remove outer parentheses if they wrap the entire expression
            if expr.startswith('(') and expr.endswith(')'):
                # Check if these are the outermost parens
                depth = 0
                for i, c in enumerate(expr):
                    if c == '(':
                        depth += 1
                    elif c == ')':
                        depth -= 1
                    if depth == 0 and i < len(expr) - 1:
                        break
                if i == len(expr) - 1:
                    expr = expr[1:-1].strip()
            
            # Handle implication (lowest precedence)
            depth = 0
            for i in range(len(expr) - 1, -1, -1):
                if expr[i] == '(':
                    depth += 1
                elif expr[i] == ')':
                    depth -= 1
                elif depth == 0 and i > 0 and expr[i-1:i+1] == '=>':
                    left = parse_boolean_expr(expr[:i-1])
                    right = parse_boolean_expr(expr[i+1:])
                    return f"(=> {left} {right})"
            
            # Handle OR (next precedence)
            depth = 0
            for i in range(len(expr)):
                if expr[i] == '(':
                    depth += 1
                elif expr[i] == ')':
                    depth -= 1
                elif depth == 0 and expr[i] == '|':
                    left = parse_boolean_expr(expr[:i])
                    right = parse_boolean_expr(expr[i+1:])
                    return f"(or {left} {right})"
            
            # Handle AND (next precedence)
            depth = 0
            for i in range(len(expr)):
                if expr[i] == '(':
                    depth += 1
                elif expr[i] == ')':
                    depth -= 1
                elif depth == 0 and expr[i] == '&':
                    left = parse_boolean_expr(expr[:i])
                    right = parse_boolean_expr(expr[i+1:])
                    return f"(and {left} {right})"
            
            # Handle NOT (highest precedence)
            if expr.startswith('!'):
                inner = parse_boolean_expr(expr[1:])
                return f"(not {inner})"
            
            # Base case: feature name (including quoted names)
            return expr
        
        return parse_boolean_expr(constraint)

    def _arithmetic_to_smt(self, constraint):
        """Convert arithmetic constraint to SMT-LIB format."""

        # First expand aggregate functions
        constraint = self._expand_aggregates(constraint)

        # Find the comparison operator and split
        comp_ops = ["==", "!=", "<=", ">=", "<", ">"]
        for op in comp_ops:
            if op in constraint:
                parts = constraint.split(op, 1)
                left = parts[0].strip()
                right = parts[1].strip()

                smt_op = "=" if op == "==" else "distinct" if op == "!=" else op
                left_smt = self._expr_to_smt(left)
                right_smt = self._expr_to_smt(right)

                return f"({smt_op} {left_smt} {right_smt})"

        return constraint

    def _expand_aggregates(self, constraint):
        """Expand aggregate functions like sum(attr), avg(attr), and len(feature).

        For optional features, generates conditional SMT expressions using ite:
        - sum(Price) with optional features B, C: A.Price + (ite B B.Price 0) + (ite C C.Price 0)
        - avg(Price): sum / count_of_selected_features
        - len(feature): (str.len feature_val)

        Returns the expanded constraint with SMT ite expressions in prefix notation.
        """

        agg_pattern = r"(sum|avg|len)\(([A-Za-z_]\w*)\)"

        def expand_aggregate(match):
            func, attr_name = match.group(1), match.group(2)

            # String length function
            if func == "len":
                return f"strlen_{attr_name}"

            # Build list of attribute references with conditionals for optional features
            feature_attrs = []
            for feature in self.features:
                if (
                    feature in self.feature_attributes and attr_name in self.feature_attributes[feature]
                ):
                    attr_ref = f"{feature}.{attr_name}"
                    if self._is_feature_optional(feature):
                        # Optional: include only if selected
                        feature_attrs.append(f"(ite {feature} {attr_ref} 0)")
                    else:
                        # Mandatory: always include
                        feature_attrs.append(attr_ref)

            if not feature_attrs:
                # Fallback for undeclared attributes
                feature_attrs = [f"{f}.{attr_name}" for f in self.features]

            # Generate expression based on aggregate type
            if func == "sum":
                return " + ".join(feature_attrs)

            elif func == "avg":
                sum_expr = " + ".join(feature_attrs)
                # Count only selected features
                count_terms = []
                for feature in self.features:
                    if (
                        feature in self.feature_attributes
                        and attr_name in self.feature_attributes[feature]
                    ):
                        if self._is_feature_optional(feature):
                            count_terms.append(f"(ite {feature} 1 0)")
                        else:
                            count_terms.append("1")

                count_expr = (
                    " + ".join(count_terms) if count_terms else str(len(feature_attrs))
                )
                return f"(({sum_expr}) / ({count_expr}))"

            return match.group(0)

        return re.sub(agg_pattern, expand_aggregate, constraint)

    def _is_feature_optional(self, feature_name):
        """Determine if a feature is optional based on feature hierarchy.

        Returns:
            bool: True if feature is optional, False if mandatory or root
        """
        builder = self.builder()

        if feature_name == builder.root_feature:
            return False

        for parent, info in builder.feature_hierarchy.items():
            for child, child_type in info.get("children", []):
                if child == feature_name:
                    return child_type == "optional"

        return True  # Default to optional for safety

    def _expr_to_smt(self, expr):
        """Convert infix arithmetic expression to SMT-LIB 2.0 prefix notation.

        Handles:
        - Arithmetic operators: +, -, *, /
        - Parentheses and operator precedence
        - SMT prefix expressions (ite, str.len, etc.) - preserved as-is
        - String length: strlen_feature -> (str.len feature_val)

        SMT prefix expressions like (ite cond then else) are recognized by checking
        if the first token after '(' is a known SMT function.

        Args:
            expr: Expression string in mixed infix/prefix notation

        Returns:
            Expression string in pure SMT-LIB prefix notation
        """

        expr = expr.strip()

        # Check if this is an SMT prefix expression (starts with known SMT function)
        if expr.startswith("("):
            # Extract first token after opening paren
            match = re.match(r"\(([a-z_]+)\s", expr)
            if match and match.group(1) in [
                "ite",
                "str.len",
                "and",
                "or",
                "not",
                "str.++",
            ]:
                # This is already an SMT prefix form, recursively convert its arguments
                return self._convert_smt_prefix_args(expr)

        # Remove outer parentheses if they wrap the entire expression
        if expr.startswith("(") and expr.endswith(")"):
            depth = 0
            for i, c in enumerate(expr):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                if depth == 0 and i < len(expr) - 1:
                    break
            if i == len(expr) - 1:
                return self._expr_to_smt(expr[1:-1])

        # Parse infix operators with proper precedence
        # Track depth to skip over SMT prefix expressions
        depth = 0

        # Handle addition and subtraction (lowest precedence)
        for i in range(len(expr) - 1, -1, -1):
            if expr[i] == ")":
                depth += 1
            elif expr[i] == "(":
                depth -= 1
            elif depth == 0 and expr[i] in ["+", "-"] and i > 0:
                left = self._expr_to_smt(expr[:i].strip())
                right = self._expr_to_smt(expr[i + 1 :].strip())
                return f"({expr[i]} {left} {right})"

        # Handle multiplication and division (higher precedence)
        depth = 0
        for i in range(len(expr) - 1, -1, -1):
            if expr[i] == ")":
                depth += 1
            elif expr[i] == "(":
                depth -= 1
            elif depth == 0 and expr[i] in ["*", "/"]:
                left = self._expr_to_smt(expr[:i].strip())
                right = self._expr_to_smt(expr[i + 1 :].strip())
                return f"({expr[i]} {left} {right})"

        # Handle string length function
        if expr.startswith("strlen_"):
            feature = expr[7:]
            if (
                feature in self.feature_types
                and "String" in self.feature_types[feature]
            ):
                return f"(str.len {feature}_val)"
            return f"(str.len {feature})"

        # Handle string literals (convert single quotes to double quotes)
        if expr.startswith("'") and expr.endswith("'"):
            return f'"{expr[1:-1]}"'

        # Handle String-typed features (convert to _val reference)
        if expr in self.feature_types and "String" in self.feature_types[expr]:
            return f"{expr}_val"

        # Base case: atomic expression (number, variable, or complete SMT prefix form)
        return expr

    def _convert_smt_prefix_args(self, expr):
        """Recursively convert arguments inside SMT prefix expressions.

        For example: (ite B B.Price + A.Price 0) -> (ite B (+ B.Price A.Price) 0)
        """

        # Match: (function arg1 arg2 ...)
        match = re.match(r"\(([a-z_]+)\s+(.+)\)$", expr, re.DOTALL)
        if not match:
            return expr

        func = match.group(1)
        args_str = match.group(2).strip()

        # Split arguments, respecting nested parentheses
        args = []
        current_arg = []
        depth = 0

        for char in args_str:
            if char == "(":
                depth += 1
                current_arg.append(char)
            elif char == ")":
                depth -= 1
                current_arg.append(char)
            elif char == " " and depth == 0:
                if current_arg:
                    args.append("".join(current_arg))
                    current_arg = []
            else:
                current_arg.append(char)

        if current_arg:
            args.append("".join(current_arg))

        # Recursively convert each argument
        converted_args = [self._expr_to_smt(arg) for arg in args]

        return f"({func} {' '.join(converted_args)})"


# =============================================================================
# Parser Implementation Classes
# =============================================================================


class BaseFeatureExtractor:
    """Base class for feature and constraint extraction."""

    def __init__(self):
        self.features = []
        self.boolean_constraints = []
        self.arithmetic_constraints = []
        self.feature_types = {}
        self.feature_attributes = {}  # {feature: {attr_name: value}}
        # Tier 1 non-Boolean-language-level counts -- see
        # docs/non_boolean_support.md. Tier 3 (typed_features/
        # attributed_features) isn't tracked incrementally: it's just
        # len(feature_types)/len(feature_attributes), computed by whoever
        # assembles the full non_boolean dict (UVL._parse).
        self.cardinality_feature_count = 0
        self.constraint_attribute_count = 0

    def add_feature(self, feature_name, feature_type=None):
        self.features.append(feature_name)
        if feature_type:
            self.feature_types[feature_name] = feature_type

    def mark_feature_cardinality(self):
        """A feature declares a clone cardinality ([i..j]) -- Tier 1,
        not decorative: it needs real subtree duplication to be encoded
        correctly, which nothing here does (see docs/non_boolean_support.md).
        """
        self.cardinality_feature_count += 1

    def mark_constraint_attribute(self):
        """A feature-local `{constraint ...}`/`{constraints [...]}`
        attribute was seen and skipped -- Tier 1: a real constraint is
        silently lost, not just metadata.
        """
        self.constraint_attribute_count += 1

    def add_attribute(self, feature_name, attr_name, attr_value):
        """Add an attribute value for a feature."""
        if feature_name not in self.feature_attributes:
            self.feature_attributes[feature_name] = {}
        self.feature_attributes[feature_name][attr_name] = attr_value

    def add_constraint(self, constraint_text):
        if _is_arithmetic_constraint(constraint_text):
            self.arithmetic_constraints.append(constraint_text)
        else:
            self.boolean_constraints.append(constraint_text)


def _is_arithmetic_constraint(constraint_text):
    """True if `constraint_text` is a bare comparison (not convertible to
    CNF), false if it's boolean-encodable. Shared by every backend's
    constraint classification -- Lark/ANTLR via BaseFeatureExtractor.add_constraint
    above, zig via UVL._ensure_zig_full below -- so all three agree by
    construction rather than by keeping separate implementations in sync.
    """
    has_boolean_op = any(op in constraint_text for op in ["=>", "<=>"])
    has_arithmetic_op = any(
        op in constraint_text for op in ["==", "!=", "<=", ">=", "<", ">"]
    )
    return has_arithmetic_op and not has_boolean_op


class LarkFeatureExtractor(BaseFeatureExtractor):
    """Lark-specific feature extractor."""

    def visit(self, tree):
        if not isinstance(tree, Tree):
            return

        if tree.data == "feature":
            self._visit_feature(tree)
        elif tree.data == "constraint_line":
            self._visit_constraint_line(tree)

        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

    def _visit_feature(self, tree):
        feature_name = None
        for child in tree.children:
            if isinstance(child, Tree) and child.data == "reference":
                feature_name = _get_text(child)
                self.add_feature(feature_name)

                for sibling in tree.children:
                    if isinstance(sibling, Tree) and sibling.data == "feature_type":
                        self.feature_types[feature_name] = _get_text(sibling)
                    elif (
                        isinstance(sibling, Tree)
                        and sibling.data == "feature_cardinality"
                    ):
                        self.mark_feature_cardinality()
                break

        # Extract attributes
        if feature_name:
            for child in tree.children:
                if isinstance(child, Tree) and child.data == "attributes":
                    self._extract_attributes(feature_name, child)

    def _extract_attributes(self, feature_name, attrs_tree):
        """Extract attribute key-value pairs from attributes tree."""
        for child in attrs_tree.children:
            if isinstance(child, Tree) and child.data == "attribute":
                for subchild in child.children:
                    if (
                        isinstance(subchild, Tree)
                        and subchild.data == "value_attribute"
                    ):
                        key = None
                        value = None
                        for item in subchild.children:
                            if isinstance(item, Tree) and item.data == "key":
                                key = _get_text(item)
                            elif isinstance(item, Tree) and item.data == "value":
                                value = _get_text(item)
                        if key and value:
                            self.add_attribute(feature_name, key, value)
                    elif (
                        isinstance(subchild, Tree)
                        and subchild.data == "constraint_attribute"
                    ):
                        self.mark_constraint_attribute()

    def _visit_constraint_line(self, tree):
        self.add_constraint(_get_text(tree))


class AntlrFeatureExtractor(BaseFeatureExtractor, uvl_python_parserListener):
    """ANTLR-specific feature extractor."""

    def __init__(self):
        super().__init__()
        self._current_feature = None

    def enterFeature(self, ctx):
        if ctx.reference():
            feature_name = ctx.reference().getText()
            self._current_feature = feature_name
            feature_type = ctx.featureType().getText() if ctx.featureType() else None
            self.add_feature(feature_name, feature_type)
            if ctx.featureCardinality():
                self.mark_feature_cardinality()

    def exitFeature(self, ctx):
        self._current_feature = None

    def enterValueAttribute(self, ctx):
        """Extract value attributes for the current feature."""
        if not self._current_feature:
            return

        if ctx.key() and ctx.value():
            key = ctx.key().getText()
            value = ctx.value().getText()
            self.add_attribute(self._current_feature, key, value)

    def enterSingleConstraintAttribute(self, ctx):
        self.mark_constraint_attribute()

    def enterListConstraintAttribute(self, ctx):
        self.mark_constraint_attribute()

    def enterConstraintLine(self, ctx):
        self.add_constraint(ctx.constraint().getText())


class _ZigBuilder:
    """UVL.builder()'s return value for backend="zig". Exposes exactly the
    two attributes to_cnf()/to_smt() actually read on a builder
    (.root_feature/.feature_hierarchy, matching BaseFeatureModelBuilder's
    shape) -- backed by uvllang._zig.parse_source_full's already-decoded
    dict rather than a Lark/ANTLR tree walk.
    """

    def __init__(self, root_feature, feature_hierarchy):
        self.root_feature = root_feature
        self.feature_hierarchy = feature_hierarchy


class BaseFeatureModelBuilder:
    """Base class for building feature model hierarchy."""

    def __init__(self):
        self.root_feature = None
        self.feature_hierarchy = {}
        self.current_feature = None
        self.feature_stack = []
        self.current_group = None
        self.group_stack = []
        # Tier 1 -- see docs/non_boolean_support.md. A cardinality group's
        # members already become plain optional children with no group
        # entry (below/in the Lark/ANTLR subclasses), matching Zig; this
        # just counts how many times that happened.
        self.cardinality_group_count = 0

    def mark_cardinality_group(self):
        self.cardinality_group_count += 1

    def _start_feature(self, feature_name):
        if self.root_feature is None:
            self.root_feature = feature_name

        if feature_name not in self.feature_hierarchy:
            self.feature_hierarchy[feature_name] = {
                "parent": self.current_feature,
                "children": [],
                "groups": [],
            }

        child_type = "optional"
        if self.current_group and self.current_group[0] == "mandatory_children":
            child_type = "mandatory"

        if self.current_group:
            self.current_group[1].append(feature_name)

        if self.current_feature:
            self.feature_hierarchy[self.current_feature]["children"].append(
                (feature_name, child_type)
            )

        self.feature_stack.append(self.current_feature)
        self.current_feature = feature_name

    def _end_feature(self):
        self.current_feature = self.feature_stack.pop() if self.feature_stack else None

    def _start_group(self, group_type):
        if self.current_feature:
            self.current_group = (group_type, [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]["groups"].append(
                self.current_group
            )

    def _end_group(self):
        if self.group_stack:
            self.group_stack.pop()
        self.current_group = self.group_stack[-1] if self.group_stack else None


class LarkFeatureModelBuilder(BaseFeatureModelBuilder):
    """Lark-specific feature model builder."""

    def visit(self, tree):
        if not isinstance(tree, Tree):
            return

        if tree.data == "feature":
            self._visit_feature(tree)
        elif tree.data == "or_group":
            self._visit_group(tree, "or")
        elif tree.data == "alternative_group":
            self._visit_group(tree, "xor")
        elif tree.data == "optional_group":
            self._visit_group(tree, "optional_children")
        elif tree.data == "mandatory_group":
            self._visit_group(tree, "mandatory_children")
        elif tree.data == "cardinality_group":
            # Never wrapped in a group entry -- see builder.zig's mirrored
            # comment -- but still counted (Tier 1: the [i..j] bound isn't
            # enforced anywhere in the resulting CNF).
            self.mark_cardinality_group()
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)
        else:
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)

    def _visit_feature(self, tree):
        feature_name = None
        for child in tree.children:
            if isinstance(child, Tree) and child.data == "reference":
                feature_name = _get_text(child)
                break

        if not feature_name:
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)
            return

        self._start_feature(feature_name)

        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        self._end_feature()

    def _visit_group(self, tree, group_type):
        self._start_group(group_type)

        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        self._end_group()


class AntlrFeatureModelBuilder(BaseFeatureModelBuilder, uvl_python_parserListener):
    """ANTLR-specific feature model builder."""

    def enterFeature(self, ctx):
        self._start_feature(ctx.reference().getText())

    def exitFeature(self, ctx):
        self._end_feature()

    def enterOrGroup(self, ctx):
        self._start_group("or")

    def enterAlternativeGroup(self, ctx):
        self._start_group("xor")

    def enterMandatoryGroup(self, ctx):
        self._start_group("mandatory_children")

    def enterOptionalGroup(self, ctx):
        self._start_group("optional_children")

    def exitOrGroup(self, ctx):
        self._end_group()

    def exitAlternativeGroup(self, ctx):
        self._end_group()

    def exitMandatoryGroup(self, ctx):
        self._end_group()

    def exitOptionalGroup(self, ctx):
        self._end_group()

    def enterCardinalityGroup(self, ctx):
        # Deliberately no _start_group/_end_group -- the walker still
        # recurses into this context's children regardless (ParseTreeWalker
        # always walks the full tree), so its members become plain
        # optional children with no group entry, matching Lark/Zig. Just
        # counted (Tier 1).
        self.mark_cardinality_group()


def _get_text(tree):
    """Extract text from a Lark tree node."""
    if isinstance(tree, Token):
        return str(tree)
    elif isinstance(tree, Tree):
        return "".join(_get_text(child) for child in tree.children)
    else:
        return str(tree)


def _load_lark_parser():
    """Load the Lark parser from grammar file."""
    grammar_path = os.path.join(os.path.dirname(__file__), "..", "grammars", "uvl.lark")

    with open(grammar_path, "r") as f:
        grammar = f.read()

    return Lark(
        grammar,
        parser="earley",
        start="start",
        propagate_positions=True,
        maybe_placeholders=False,
        ambiguity="explicit",
    )

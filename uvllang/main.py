import re
import os

from pysat.formula import CNF

from lark import Tree, Token, Lark

from uvllang.uvl_lark_lexer import UVLIndentationLexer

try:
    from antlr4 import CommonTokenStream, FileStream
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


class UVL:
    def __init__(self, from_file=None, from_str=None, use_antlr=False):
        # Exactly one of from_file or from_str must be specified
        if from_file is None and from_str is None:
            raise ValueError("Either from_file or from_str parameter is required")
        if from_file is not None and from_str is not None:
            raise ValueError("Cannot specify both from_file and from_str parameters")

        if use_antlr and not ANTLR_AVAILABLE:
            raise ImportError(
                "ANTLR parser requested but ANTLR dependencies not available. "
                "Install with: pip install uvllang[antlr]"
            )

        self._use_antlr = use_antlr
        self._file_path = from_file
        self._content = from_str
        self._tree = None
        self._extractor = None
        self._builder = None
        self._parse()

    @classmethod
    def visit(
        cls,
        feature,
        clauses,
        implies,
        implied_by,
        groups,
        ids2features,
        indent,
        dump,
        seen=None,
    ):

        if seen is None:
            seen = set()

        if feature in seen:
            return dump

        seen.add(feature)

        dump.append((indent + 4, ids2features[feature]))

        childs = implied_by.get(feature, set()).difference(seen)

        if feature in groups:
            childs_l = sorted(groups[feature])
            xor = True
            for i, child in enumerate(childs_l):
                for child2 in childs_l[i + 1 :]:
                    if (mutex := sorted([-child, -child2], key=abs)) not in clauses:
                        xor = False
                        break
                if not xor:
                    break

            if xor:
                dump.append((indent + 8, "alternative"))
            else:
                dump.append((indent + 8, "or"))

            for child in childs_l:
                dump = cls.visit(
                    child,
                    clauses,
                    implies,
                    implied_by,
                    groups,
                    ids2features,
                    indent + 8,
                    dump,
                    seen,
                )

        else:
            mandatory = childs.intersection(implies.get(feature, set()))

            if mandatory:
                dump.append((indent + 8, "mandatory"))
                for child in mandatory:
                    dump = cls.visit(
                        child,
                        clauses,
                        implies,
                        implied_by,
                        groups,
                        ids2features,
                        indent + 8,
                        dump,
                        seen,
                    )

            optional = childs.difference(mandatory)
            if optional:
                dump.append((indent + 8, "optional"))
                for child in optional:
                    dump = cls.visit(
                        child,
                        clauses,
                        implies,
                        implied_by,
                        groups,
                        ids2features,
                        indent + 8,
                        dump,
                        seen,
                    )

        return dump

    @classmethod
    def from_cnf(cls, filepath, file_out):

        cnf = CNF(from_file=filepath)

        ids2features = {}
        for comment in cnf.comments:
            split = re.split(r"\s+", comment.strip())

            if len(split[2:]) > 1:
                name = " ".join(split[2:]).strip()
                if name.startswith('"') and name.endswith('"'):
                    ids2features[int(split[1])] = name
                else:
                    ids2features[int(split[1])] = f'"{name}"'
            else:
                ids2features[int(split[1])] = " ".join(split[2:])

        # Analyze CNF structure to recover hierarchy
        clauses = [sorted(clause, key=abs) for clause in cnf.clauses]

        # Find implications: [-a, b] means a => b
        implies = {}  # a -> set of b where a => b

        # Find group constraints: [-parent, child1, child2, ...] means parent => (child1 | child2 | ...)
        groups = {}

        for clause in clauses:
            if len(clause) == 2:
                a, b = sorted(clause)
                if a < 0 and b > 0:
                    # [-a, b] means a => b
                    implies[abs(a)] = implies.get(abs(a), set())
                    implies[abs(a)].add(b)
            elif len(clause) > 2:
                # Check if it's a group constraint: one negative, rest positive
                negatives = [x for x in clause if x < 0]
                if len(negatives) == 1:
                    parent = abs(negatives[0])
                    children = {x for x in clause if x > 0}
                    groups[parent] = children

        # Build parent-child relationships from:
        # 1. Group relationships (or/alternative): definitive parent-child from at-least-one clauses
        # 2. Binary implications (child => parent): child can only exist under parent

        # Track which features have been assigned as children
        assigned_children = set()
        implied_by = {}  # parent -> children

        # Priority 1: Add all children from group relationships (most definitive)
        for parent, children in groups.items():
            implied_by[parent] = implied_by.get(parent, set())
            implied_by[parent].update(children)
            assigned_children.update(children)

        # Priority 2: Add children from binary implications (child => parent)
        # Each child should only be assigned to ONE parent
        # For bidirectional relationships, choose the more connected feature as parent
        for child, targets in implies.items():
            if child not in assigned_children:
                # Filter out targets where there's a bidirectional relationship AND target has fewer connections
                filtered_targets = []
                for p in targets:
                    # Check if bidirectional
                    if child in implies.get(p, set()):
                        # Bidirectional - only keep if parent is more connected
                        parent_connections = len(implies.get(p, set()))
                        child_connections = len(implies.get(child, set()))
                        if parent_connections >= child_connections:
                            filtered_targets.append(p)
                    else:
                        # Unidirectional - keep it
                        filtered_targets.append(p)

                if not filtered_targets:
                    continue

                # Choose best parent: prefer those in groups, with fewer incoming edges, with more children
                def parent_priority(p):
                    in_group = 1 if p in groups else 0
                    incoming_count = sum(1 for c, ts in implies.items() if p in ts)
                    has_children = 1 if p in implied_by else 0
                    return (in_group, -incoming_count, has_children, -p)

                parent = max(filtered_targets, key=parent_priority)
                implied_by[parent] = implied_by.get(parent, set())
                implied_by[parent].add(child)
                assigned_children.add(child)

        # Find root(s) - features with unit clauses
        roots = []
        for clause in clauses:
            if len(clause) == 1 and clause[0] > 0:
                roots.append(clause[0])

        if not roots:
            # No root found, shouldn't happen with valid feature model
            raise ValueError("No root feature found in CNF")

        # Build the feature tree
        seen = set()
        dump = [(0, "features")]

        for root in roots:
            dump = cls.visit(
                root, clauses, implies, implied_by, groups, ids2features, 0, dump, seen
            )

        # Add any features that weren't visited (orphaned features) as optional children of root
        all_features = set(ids2features.keys())
        unvisited = all_features - seen
        if unvisited:
            # Add them as optional children of the first root
            if roots:
                dump.append((8, "optional"))
                for feature_id in sorted(unvisited):
                    dump.append((12, ids2features[feature_id]))

        # Convert dump to string
        ls = []
        for indent, line in dump:
            ls.append(f'{" " * indent}{line}')
        s = "\n".join(ls)

        # Now convert back to CNF with same feature mapping and find remaining constraints
        uvl = UVL(from_str=s)
        features2ids = {v: k for k, v in ids2features.items()}

        recovered_clauses = uvl.to_cnf(features2ids, verbose_info=False).clauses

        # Find clauses in original that aren't in recovered (these are cross-tree constraints)
        recovered_set = {tuple(sorted(c, key=abs)) for c in recovered_clauses}
        remaining = []

        for clause in clauses:
            normalized = tuple(sorted(clause, key=abs))
            if normalized not in recovered_set:
                remaining.append(clause)

        # Add cross-tree constraints
        if remaining:
            s += "\n\nconstraints\n"
            for clause in remaining:
                constraint = []
                for lit in clause:
                    if lit < 0:
                        constraint.append(f"!{ids2features[abs(lit)]}")
                    else:
                        constraint.append(f"{ids2features[abs(lit)]}")
                constraint_str = " | ".join(constraint)
                s += f"    {constraint_str}\n"

        # Write to file
        with open(file_out, "w+") as fp:
            fp.write(s)

    def _parse(self):
        if self._use_antlr:
            if self._file_path:
                input_stream = FileStream(self._file_path)
            else:
                from antlr4 import InputStream

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
            if self._file_path:
                with open(self._file_path, "r", encoding="utf-8") as f:
                    content = f.read()
            else:
                content = self._content

            lexer = UVLIndentationLexer()
            processed_content = lexer.process(content)

            parser = _load_lark_parser()
            self._tree = parser.parse(processed_content)

            self._extractor = LarkFeatureExtractor()
            self._builder = LarkFeatureModelBuilder()
            self._extractor.visit(self._tree)
            self._builder.visit(self._tree)

    @property
    def tree(self):
        return self._tree

    @property
    def features(self):
        return self._extractor.features

    @property
    def constraints(self):
        return self.boolean_constraints + self.arithmetic_constraints

    @property
    def boolean_constraints(self):
        """Boolean constraints convertible to CNF."""
        return self._extractor.boolean_constraints

    @property
    def arithmetic_constraints(self):
        """Arithmetic constraints not convertible to CNF."""
        return self._extractor.arithmetic_constraints

    @property
    def feature_types(self):
        """Feature type annotations."""
        return self._extractor.feature_types

    @property
    def feature_attributes(self):
        """Feature attributes with their values."""
        return self._extractor.feature_attributes

    def builder(self):
        """Feature hierarchy builder."""
        return self._builder

    def to_cnf(self, features2ids=None, verbose_info=True):
        builder = self.builder()

        # sort features by name to make ids persistent regardless of hierarchy
        if features2ids is None:
            features2ids = {
                feature: i + 1 for i, feature in enumerate(sorted(self.features))
            }

        clauses = []

        # add CNF clause for the root feature
        if builder.root_feature:
            clauses.append([features2ids[builder.root_feature]])

        # add CNF clauses for hierachical dependencies
        clauses.extend(self._hierarchy_to_cnf(builder.feature_hierarchy, features2ids))

        # add CNF clauses for Boolean cross-tree constraints
        if self.boolean_constraints:
            clauses.extend(
                self._constraints_to_cnf(self.boolean_constraints, features2ids)
            )

        # TODO: This should be add to some logging
        if verbose_info and self.arithmetic_constraints:
            print(
                f"Info: Ignored {len(self.arithmetic_constraints)} arithmetic constraints"
            )

        cnf = CNF(from_clauses=clauses)
        cnf.comments = [
            f"c {feature_id} {feature_name}"
            for feature_name, feature_id in features2ids.items()
        ]

        return cnf

    def _hierarchy_to_cnf(self, hierarchy, features2ids):
        clauses = []

        for feature, info in hierarchy.items():
            feature_id = features2ids[feature]

            for child, child_type in info["children"]:
                child_id = features2ids[child]
                clauses.append([-child_id, feature_id])
                if child_type == "mandatory":
                    clauses.append([-feature_id, child_id])

            for group_type, group_members in info["groups"]:
                member_ids = [features2ids[member] for member in group_members]

                if group_type == "or":
                    clauses.append([-feature_id] + member_ids)

                elif group_type == "xor":
                    clauses.append([-feature_id] + member_ids)
                    for i in range(len(member_ids)):
                        for j in range(i + 1, len(member_ids)):
                            clauses.append([-member_ids[i], -member_ids[j]])

        return clauses

    def _constraints_to_cnf(self, constraints, features2ids):
        """Convert UVL constraints to CNF using direct conversion (no sympy)."""
        clauses = []

        for constraint_str in constraints:
            try:
                # Clean up the constraint string
                constraint_str = constraint_str.strip()

                # Check if this is a pure boolean constraint
                # Skip if it contains attribute references (.)
                # or arithmetic comparisons that are not part of =>
                temp_str = constraint_str.replace(
                    "=>", ""
                )  # Remove implication operator
                if "." in constraint_str:
                    print(
                        f"Info: Skipping constraint with attribute reference: '{constraint_str}'"
                    )
                    continue
                if any(op in temp_str for op in [">", "<", "==", "!="]):
                    print(
                        f"Info: Skipping constraint with arithmetic comparison: '{constraint_str}'"
                    )
                    continue

                # Parse and convert to CNF
                expr = self._parse_boolean_expr(constraint_str, features2ids)
                cnf_clauses = self._to_cnf(expr, features2ids)
                clauses.extend(cnf_clauses)

            except Exception as e:
                print(f"Warning: Could not convert constraint '{constraint_str}': {e}")

        return clauses

    def _parse_boolean_expr(self, expr_str, features2ids):
        """Parse a boolean expression into an AST."""
        expr_str = expr_str.strip()

        # Handle implication (lowest precedence)
        depth = 0
        for i in range(len(expr_str) - 1, -1, -1):
            if expr_str[i] == "(":
                depth += 1
            elif expr_str[i] == ")":
                depth -= 1
            elif depth == 0 and i > 0 and expr_str[i - 1 : i + 1] == "=>":
                left = self._parse_boolean_expr(expr_str[: i - 1], features2ids)
                right = self._parse_boolean_expr(expr_str[i + 1 :], features2ids)
                return ("IMPLIES", left, right)

        # Handle OR (next precedence)
        depth = 0
        for i in range(len(expr_str)):
            if expr_str[i] == "(":
                depth += 1
            elif expr_str[i] == ")":
                depth -= 1
            elif depth == 0 and expr_str[i] == "|":
                left = self._parse_boolean_expr(expr_str[:i], features2ids)
                right = self._parse_boolean_expr(expr_str[i + 1 :], features2ids)
                return ("OR", left, right)

        # Handle AND (next precedence)
        depth = 0
        for i in range(len(expr_str)):
            if expr_str[i] == "(":
                depth += 1
            elif expr_str[i] == ")":
                depth -= 1
            elif depth == 0 and expr_str[i] == "&":
                left = self._parse_boolean_expr(expr_str[:i], features2ids)
                right = self._parse_boolean_expr(expr_str[i + 1 :], features2ids)
                return ("AND", left, right)

        # Handle NOT (highest precedence)
        if expr_str.startswith("!"):
            inner = self._parse_boolean_expr(expr_str[1:], features2ids)
            return ("NOT", inner)

        # Remove outer parentheses if they wrap the entire expression
        if expr_str.startswith("(") and expr_str.endswith(")"):
            depth = 0
            for i, c in enumerate(expr_str):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                if depth == 0 and i < len(expr_str) - 1:
                    break
            if i == len(expr_str) - 1:
                return self._parse_boolean_expr(expr_str[1:-1], features2ids)

        # Base case: feature name (literal)
        feature_name = expr_str.strip()
        if feature_name not in features2ids:
            raise ValueError(f"Unknown feature: {feature_name}")
        return ("LIT", features2ids[feature_name])

    def _to_cnf(self, expr, features2ids):
        """Convert boolean expression AST to CNF clauses.

        Uses standard logical equivalences:
        - A => B  ≡  ~A | B
        - ~(A & B)  ≡  ~A | ~B  (De Morgan)
        - ~(A | B)  ≡  ~A & ~B  (De Morgan)
        - A & (B | C)  ≡  (A & B) | (A & C)  (Distribution)
        """
        # First, eliminate implications and move negations inward (NNF)
        nnf = self._to_nnf(expr)
        # Then distribute OR over AND to get CNF
        cnf = self._distribute(nnf)
        # Extract clauses from CNF
        return self._extract_clauses(cnf)

    def _to_nnf(self, expr):
        """Convert to Negation Normal Form (eliminate => and push NOT inward)."""
        op = expr[0]

        if op == "LIT":
            return expr

        elif op == "NOT":
            inner = expr[1]
            inner_op = inner[0]

            if inner_op == "LIT":
                return expr  # NOT of literal is already NNF
            elif inner_op == "NOT":
                # Double negation
                return self._to_nnf(inner[1])
            elif inner_op == "AND":
                # De Morgan: ~(A & B) = ~A | ~B
                left = self._to_nnf(("NOT", inner[1]))
                right = self._to_nnf(("NOT", inner[2]))
                return ("OR", left, right)
            elif inner_op == "OR":
                # De Morgan: ~(A | B) = ~A & ~B
                left = self._to_nnf(("NOT", inner[1]))
                right = self._to_nnf(("NOT", inner[2]))
                return ("AND", left, right)
            elif inner_op == "IMPLIES":
                # ~(A => B) = ~(~A | B) = A & ~B
                left = self._to_nnf(inner[1])
                right = self._to_nnf(("NOT", inner[2]))
                return ("AND", left, right)

        elif op == "AND":
            left = self._to_nnf(expr[1])
            right = self._to_nnf(expr[2])
            return ("AND", left, right)

        elif op == "OR":
            left = self._to_nnf(expr[1])
            right = self._to_nnf(expr[2])
            return ("OR", left, right)

        elif op == "IMPLIES":
            # A => B  ≡  ~A | B
            left = self._to_nnf(("NOT", expr[1]))
            right = self._to_nnf(expr[2])
            return ("OR", left, right)

        return expr

    def _distribute(self, expr):
        """Distribute OR over AND to get CNF."""
        op = expr[0]

        if op in ("LIT", "NOT"):
            return expr

        elif op == "AND":
            left = self._distribute(expr[1])
            right = self._distribute(expr[2])
            return ("AND", left, right)

        elif op == "OR":
            left = self._distribute(expr[1])
            right = self._distribute(expr[2])

            # Check if we need to distribute
            left_op = left[0]
            right_op = right[0]

            if left_op == "AND":
                # (A & B) | C  ≡  (A | C) & (B | C)
                a, b = left[1], left[2]
                c = right
                return (
                    "AND",
                    self._distribute(("OR", a, c)),
                    self._distribute(("OR", b, c)),
                )

            elif right_op == "AND":
                # A | (B & C)  ≡  (A | B) & (A | C)
                a = left
                b, c = right[1], right[2]
                return (
                    "AND",
                    self._distribute(("OR", a, b)),
                    self._distribute(("OR", a, c)),
                )

            else:
                return ("OR", left, right)

        return expr

    def _extract_clauses(self, cnf):
        """Extract clauses from CNF expression."""
        clauses = []

        def extract(expr):
            op = expr[0]

            if op == "AND":
                extract(expr[1])
                extract(expr[2])
            else:
                # This is a single clause (OR of literals or a single literal)
                clause = self._extract_literals(expr)
                clauses.append(clause)

        extract(cnf)
        return clauses

    def _extract_literals(self, expr):
        """Extract literals from a clause (OR expression or single literal)."""
        literals = []

        def extract(e):
            op = e[0]

            if op == "LIT":
                literals.append(e[1])
            elif op == "NOT":
                # NOT of a literal
                inner = e[1]
                if inner[0] == "LIT":
                    literals.append(-inner[1])
                else:
                    raise ValueError("NOT should only be applied to literals in CNF")
            elif op == "OR":
                extract(e[1])
                extract(e[2])
            else:
                raise ValueError(f"Unexpected operator in clause: {op}")

        extract(expr)
        return literals

    def to_smt(self):
        """Convert feature model to SMT-LIB 2 format."""
        builder = self.builder()
        lines = []

        # Collect string-typed features
        string_features = set()
        for feature in self.features:
            if (
                feature in self.feature_types
                and "String" in self.feature_types[feature]
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
            if expr.startswith("(") and expr.endswith(")"):
                # Check if these are the outermost parens
                depth = 0
                for i, c in enumerate(expr):
                    if c == "(":
                        depth += 1
                    elif c == ")":
                        depth -= 1
                    if depth == 0 and i < len(expr) - 1:
                        break
                if i == len(expr) - 1:
                    expr = expr[1:-1].strip()

            # Handle implication (lowest precedence)
            depth = 0
            for i in range(len(expr) - 1, -1, -1):
                if expr[i] == "(":
                    depth += 1
                elif expr[i] == ")":
                    depth -= 1
                elif depth == 0 and i > 0 and expr[i - 1 : i + 1] == "=>":
                    left = parse_boolean_expr(expr[: i - 1])
                    right = parse_boolean_expr(expr[i + 1 :])
                    return f"(=> {left} {right})"

            # Handle OR (next precedence)
            depth = 0
            for i in range(len(expr)):
                if expr[i] == "(":
                    depth += 1
                elif expr[i] == ")":
                    depth -= 1
                elif depth == 0 and expr[i] == "|":
                    left = parse_boolean_expr(expr[:i])
                    right = parse_boolean_expr(expr[i + 1 :])
                    return f"(or {left} {right})"

            # Handle AND (next precedence)
            depth = 0
            for i in range(len(expr)):
                if expr[i] == "(":
                    depth += 1
                elif expr[i] == ")":
                    depth -= 1
                elif depth == 0 and expr[i] == "&":
                    left = parse_boolean_expr(expr[:i])
                    right = parse_boolean_expr(expr[i + 1 :])
                    return f"(and {left} {right})"

            # Handle NOT (highest precedence)
            if expr.startswith("!"):
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
                    feature in self.feature_attributes
                    and attr_name in self.feature_attributes[feature]
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

    def add_feature(self, feature_name, feature_type=None):
        self.features.append(feature_name)
        if feature_type:
            self.feature_types[feature_name] = feature_type

    def add_attribute(self, feature_name, attr_name, attr_value):
        """Add an attribute value for a feature."""
        if feature_name not in self.feature_attributes:
            self.feature_attributes[feature_name] = {}
        self.feature_attributes[feature_name][attr_name] = attr_value

    def add_constraint(self, constraint_text):
        has_boolean_op = any(op in constraint_text for op in ["=>", "<=>"])
        has_arithmetic_op = any(
            op in constraint_text for op in ["==", "!=", "<=", ">=", "<", ">"]
        )
        if has_arithmetic_op and not has_boolean_op:
            self.arithmetic_constraints.append(constraint_text)
        else:
            self.boolean_constraints.append(constraint_text)


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
                # Look for value_attribute
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

    def enterConstraintLine(self, ctx):
        self.add_constraint(ctx.constraint().getText())


class BaseFeatureModelBuilder:
    """Base class for building feature model hierarchy."""

    def __init__(self):
        self.root_feature = None
        self.feature_hierarchy = {}
        self.current_feature = None
        self.feature_stack = []
        self.current_group = None
        self.group_stack = []

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


def _get_text(tree):
    """Extract text from a Lark tree node."""
    if isinstance(tree, Token):
        return str(tree)
    elif isinstance(tree, Tree):
        return "".join(_get_text(child) for child in tree.children)
    else:
        return str(tree)


def _load_lark_parser() -> Lark:
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

import re
import os

from sympy import symbols, to_cnf, Or, And, Not
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
    """UVL feature model parser and CNF converter."""

    def __init__(self, from_file=None, use_antlr=False):
        if from_file is None:
            raise ValueError("from_file parameter is required")

        if use_antlr and not ANTLR_AVAILABLE:
            raise ImportError(
                "ANTLR parser requested but ANTLR dependencies not available. "
                "Install with: pip install uvllang[antlr]"
            )

        self._use_antlr = use_antlr
        self._file_path = from_file
        self._tree = None
        self._extractor = None
        self._builder = None
        self._parse_file()

    def _parse_file(self):
        if self._use_antlr:
            input_stream = FileStream(self._file_path)
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
            with open(self._file_path, "r", encoding="utf-8") as f:
                content = f.read()

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

    def to_cnf(self, verbose_info=True):
        """Convert feature model to CNF."""
        builder = self.builder()
        feature_to_id = {feature: i + 1 for i, feature in enumerate(self.features)}

        clauses = []

        if builder.root_feature:
            clauses.append([feature_to_id[builder.root_feature]])

        clauses.extend(self._hierarchy_to_cnf(builder.feature_hierarchy, feature_to_id))

        if self.boolean_constraints:
            clauses.extend(
                self._constraints_to_cnf(self.boolean_constraints, feature_to_id)
            )

        if verbose_info and self.arithmetic_constraints:
            print(
                f"Info: Ignored {len(self.arithmetic_constraints)} arithmetic constraints"
            )

        cnf = CNF(from_clauses=clauses)
        cnf.comments = [
            f"c {feature_id} {feature_name}"
            for feature_name, feature_id in feature_to_id.items()
        ]

        return cnf

    def _hierarchy_to_cnf(self, hierarchy, feature_to_id):
        """Convert hierarchy to CNF clauses."""
        clauses = []

        for feature, info in hierarchy.items():
            feature_id = feature_to_id[feature]

            for child, child_type in info["children"]:
                child_id = feature_to_id[child]
                clauses.append([-child_id, feature_id])
                if child_type == "mandatory":
                    clauses.append([-feature_id, child_id])

            for group_type, group_members in info["groups"]:
                member_ids = [feature_to_id[member] for member in group_members]

                if group_type == "or":
                    clauses.append([-feature_id] + member_ids)

                elif group_type == "xor":
                    clauses.append([-feature_id] + member_ids)
                    for i in range(len(member_ids)):
                        for j in range(i + 1, len(member_ids)):
                            clauses.append([-member_ids[i], -member_ids[j]])

        return clauses

    def _constraints_to_cnf(self, constraints, feature_to_id):
        """Convert UVL constraints to CNF using sympy."""
        clauses = []
        feature_symbols = {name: symbols(name) for name in feature_to_id.keys()}

        for constraint_str in constraints:
            try:
                expr_str = (
                    constraint_str.replace("&", " & ")
                    .replace("|", " | ")
                    .replace("!", "~")
                    .replace("=>", " >> ")
                )
                expr = eval(expr_str, {"__builtins__": {}}, feature_symbols)
                cnf_expr = to_cnf(expr, simplify=True)
                constraint_clauses = self._sympy_to_clauses(
                    cnf_expr, feature_to_id, feature_symbols
                )
                clauses.extend(constraint_clauses)
            except Exception as e:
                print(f"Warning: Could not convert constraint '{constraint_str}': {e}")

        return clauses

    def _sympy_to_clauses(self, expr, feature_to_id, feature_symbols):
        """Convert sympy CNF expression to clauses."""
        clauses = []
        symbol_to_id = {
            sym: feature_to_id[name] for name, sym in feature_symbols.items()
        }

        if expr.func == And:
            for clause in expr.args:
                clauses.append(self._parse_clause(clause, symbol_to_id))
        elif expr.func == Or:
            clauses.append(self._parse_clause(expr, symbol_to_id))
        elif expr.func == Not:
            sym = expr.args[0]
            clauses.append([-symbol_to_id[sym]])
        elif expr.is_Symbol:
            clauses.append([symbol_to_id[expr]])
        elif expr == False:
            clauses.append([])

        return clauses

    def _parse_clause(self, clause, symbol_to_id):
        """Parse clause into literals."""
        literals = []

        if clause.func == Or:
            for lit in clause.args:
                if lit.func == Not:
                    literals.append(-symbol_to_id[lit.args[0]])
                elif lit.is_Symbol:
                    literals.append(symbol_to_id[lit])
        elif clause.func == Not:
            literals.append(-symbol_to_id[clause.args[0]])
        elif clause.is_Symbol:
            literals.append(symbol_to_id[clause])

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
        result = constraint.strip()
        
        # Check if it's just a single feature name (no operators)
        if result.isidentifier():
            return result
        
        result = result.replace("!", "not ")
        result = result.replace("&", "and")
        result = result.replace("|", "or")
        result = result.replace("=>", "=>")
        result = result.replace("<=>", "=")
        # Add parentheses for operators
        result = result.replace(" and ", " (and ")
        result = result.replace(" or ", " (or ")
        result = result.replace("not ", "(not ")
        # Balance parentheses (simplified)
        return f"({result})"

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

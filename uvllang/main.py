import os
from sympy import symbols, to_cnf, Or, And, Not, Implies
from sympy.logic.boolalg import BooleanFunction
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

    def add_feature(self, feature_name, feature_type=None):
        self.features.append(feature_name)
        if feature_type:
            self.feature_types[feature_name] = feature_type

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
        for child in tree.children:
            if isinstance(child, Tree) and child.data == "reference":
                feature_name = _get_text(child)
                self.add_feature(feature_name)

                for sibling in tree.children:
                    if isinstance(sibling, Tree) and sibling.data == "feature_type":
                        self.feature_types[feature_name] = _get_text(sibling)
                break

    def _visit_constraint_line(self, tree):
        self.add_constraint(_get_text(tree))


class AntlrFeatureExtractor(BaseFeatureExtractor, uvl_python_parserListener):
    """ANTLR-specific feature extractor."""

    def enterFeature(self, ctx):
        if ctx.reference():
            feature_name = ctx.reference().getText()
            feature_type = ctx.featureType().getText() if ctx.featureType() else None
            self.add_feature(feature_name, feature_type)

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

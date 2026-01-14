from antlr4 import CommonTokenStream, FileStream
from uvllang.uvl_custom_lexer import uvl_custom_lexer
from uvllang.uvl_python_parser import uvl_python_parser
from uvllang.uvl_python_parser_listener import uvl_python_parserListener
from antlr4.error.ErrorListener import ErrorListener
from antlr4.tree.Tree import ParseTreeWalker
from sympy import symbols, to_cnf, Or, And, Not, Implies
from sympy.logic.boolalg import BooleanFunction

class CustomErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        if "\\t" in msg:
            print(f"Warning: Line {line}:{column} - {msg}")
            return
        raise Exception(f"Parse error at line {line}:{column} - {msg}")


class FeatureConstraintExtractor(uvl_python_parserListener):
    def __init__(self):
        self.features = []
        self.constraints = []

    def enterFeature(self, ctx):
        if ctx.reference():
            feature_name = ctx.reference().getText()
            self.features.append(feature_name)

    def enterConstraintLine(self, ctx):
        constraint_text = ctx.constraint().getText()
        self.constraints.append(constraint_text)


class FeatureModelBuilder(uvl_python_parserListener):
    def __init__(self):
        self.root_feature = None
        self.feature_hierarchy = {}
        self.current_feature = None
        self.feature_stack = []
        self.current_group = None
        self.group_stack = []

    def enterFeature(self, ctx):
        feature_name = ctx.reference().getText()
        
        if self.root_feature is None:
            self.root_feature = feature_name
        
        if feature_name not in self.feature_hierarchy:
            self.feature_hierarchy[feature_name] = {
                'parent': self.current_feature,
                'children': [],
                'groups': []
            }
        
        child_type = 'optional'
        if self.current_group and self.current_group[0] == 'mandatory_children':
            child_type = 'mandatory'
        
        if self.current_group:
            self.current_group[1].append(feature_name)
        
        if self.current_feature:
            self.feature_hierarchy[self.current_feature]['children'].append((feature_name, child_type))
        
        self.feature_stack.append(self.current_feature)
        self.current_feature = feature_name

    def exitFeature(self, ctx):
        self.current_feature = self.feature_stack.pop() if self.feature_stack else None

    def enterOrGroup(self, ctx):
        if self.current_feature:
            self.current_group = ('or', [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]['groups'].append(self.current_group)

    def enterAlternativeGroup(self, ctx):
        if self.current_feature:
            self.current_group = ('xor', [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]['groups'].append(self.current_group)

    def enterMandatoryGroup(self, ctx):
        if self.current_feature:
            self.current_group = ('mandatory_children', [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]['groups'].append(self.current_group)

    def enterOptionalGroup(self, ctx):
        if self.current_feature:
            self.current_group = ('optional_children', [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]['groups'].append(self.current_group)

    def exitOrGroup(self, ctx):
        if self.group_stack:
            self.group_stack.pop()
        self.current_group = self.group_stack[-1] if self.group_stack else None

    def exitAlternativeGroup(self, ctx):
        if self.group_stack:
            self.group_stack.pop()
        self.current_group = self.group_stack[-1] if self.group_stack else None

    def exitMandatoryGroup(self, ctx):
        if self.group_stack:
            self.group_stack.pop()
        self.current_group = self.group_stack[-1] if self.group_stack else None

    def exitOptionalGroup(self, ctx):
        if self.group_stack:
            self.group_stack.pop()
        self.current_group = self.group_stack[-1] if self.group_stack else None

class UVL:
    def __init__(self, from_file=None):
        if from_file is None:
            raise ValueError("from_file parameter is required")
        
        self._file_path = from_file
        self._tree = None
        self._features = None
        self._constraints = None
        self._parse_file()

    def _parse_file(self):
        input_stream = FileStream(self._file_path)
        lexer = uvl_custom_lexer(input_stream)
        lexer.removeErrorListeners()
        lexer.addErrorListener(CustomErrorListener())

        stream = CommonTokenStream(lexer)
        parser = uvl_python_parser(stream)
        parser.removeErrorListeners()
        parser.addErrorListener(CustomErrorListener())

        self._tree = parser.featureModel()

    @property
    def tree(self):
        return self._tree

    @property
    def features(self):
        if self._features is None:
            extractor = FeatureConstraintExtractor()
            walker = ParseTreeWalker()
            walker.walk(extractor, self._tree)
            self._features = extractor.features
        return self._features

    @property
    def constraints(self):
        if self._constraints is None:
            extractor = FeatureConstraintExtractor()
            walker = ParseTreeWalker()
            walker.walk(extractor, self._tree)
            self._constraints = extractor.constraints
        return self._constraints

    def to_cnf(self):
        """Convert the feature model to CNF (Conjunctive Normal Form).
        
        Returns:
            list: List of clauses, where each clause is a list of literals.
        """
        builder = FeatureModelBuilder()
        walker = ParseTreeWalker()
        walker.walk(builder, self._tree)
        
        clauses = []
        feature_to_id = {feature: i + 1 for i, feature in enumerate(self.features)}
        
        if builder.root_feature:
            root_id = feature_to_id[builder.root_feature]
            clauses.append([root_id])
        
        for feature, info in builder.feature_hierarchy.items():
            feature_id = feature_to_id[feature]
            for child, child_type in info['children']:
                if child_type == 'mandatory':
                    child_id = feature_to_id[child]
                    clauses.append([-feature_id, child_id])
        
        for feature, info in builder.feature_hierarchy.items():
            feature_id = feature_to_id[feature]
            for child, child_type in info['children']:
                child_id = feature_to_id[child]
                clauses.append([-child_id, feature_id])
        
        for feature, info in builder.feature_hierarchy.items():
            feature_id = feature_to_id[feature]
            for group_type, group_members in info['groups']:
                member_ids = [feature_to_id[member] for member in group_members]
                
                if group_type == 'or':
                    clauses.append([-feature_id] + member_ids)
                
                elif group_type == 'xor':
                    clauses.append([-feature_id] + member_ids)
                    for i in range(len(member_ids)):
                        for j in range(i + 1, len(member_ids)):
                            clauses.append([-member_ids[i], -member_ids[j]])
        
        if self.constraints:
            clauses.extend(self._constraints_to_cnf(self.constraints, feature_to_id))
        
        return clauses
    
    def _constraints_to_cnf(self, constraints, feature_to_id):
        """Convert UVL constraints to CNF clauses using sympy."""
        clauses = []
        feature_symbols = {name: symbols(name) for name in feature_to_id.keys()}
        
        for constraint_str in constraints:
            try:
                expr_str = constraint_str.replace('&', ' & ').replace('|', ' | ').replace('!', '~').replace('=>', ' >> ')
                expr = eval(expr_str, {"__builtins__": {}}, feature_symbols)
                cnf_expr = to_cnf(expr, simplify=True)
                constraint_clauses = self._sympy_to_clauses(cnf_expr, feature_to_id, feature_symbols)
                clauses.extend(constraint_clauses)
            except Exception as e:
                print(f"Warning: Could not convert constraint '{constraint_str}': {e}")
        
        return clauses
    
    def _sympy_to_clauses(self, expr, feature_to_id, feature_symbols):
        """Convert a sympy CNF expression to a list of clauses."""
        clauses = []
        symbol_to_id = {sym: feature_to_id[name] for name, sym in feature_symbols.items()}
        
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
        """Parse a single clause (disjunction) into a list of literals."""
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
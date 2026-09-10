"""ANTLR-backed UVL parsing: lazy import of antlr4 and the generated
parser, the ANTLR-specific feature/model extraction classes, and the
parse() entry point uvllang.uvl.UVL calls for backend="antlr".
"""

from uvllang.feature_extraction import BaseFeatureExtractor, BaseFeatureModelBuilder

_loaded = False


def load():
    """Lazily imports antlr4 and defines the ANTLR listener classes.
    Raises ImportError if antlr4 isn't installed.
    """
    global _loaded
    global CommonTokenStream, InputStream
    global uvl_custom_lexer, uvl_python_parser, ParseTreeWalker
    global CustomErrorListener, AntlrFeatureExtractor, AntlrFeatureModelBuilder
    if _loaded:
        return

    try:
        from antlr4 import CommonTokenStream, InputStream
        from uvllang.antlr4.uvl_custom_lexer import uvl_custom_lexer
        from uvllang.antlr4.uvl_python_parser import uvl_python_parser
        from antlr4.error.ErrorListener import ErrorListener
        from antlr4.tree.Tree import ParseTreeListener, ParseTreeWalker
    except ImportError as e:
        raise ImportError(
            "ANTLR parser requested but ANTLR dependencies not available. "
            "Install with: pip install uvllang[antlr]"
        ) from e

    class CustomErrorListener(ErrorListener):
        def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
            if "\\t" in msg:
                print(f"Warning: Line {line}:{column} - {msg}")
                return
            raise Exception(f"Parse error at line {line}:{column} - {msg}")

    # Dispatch by ctx class name in enterEveryRule/exitEveryRule, mirroring
    # LarkFeatureExtractor's tree.data dispatch (uvllang/lark/uvl_lark_parser.py).

    class AntlrFeatureExtractor(BaseFeatureExtractor, ParseTreeListener):
        """ANTLR-specific feature extractor."""

        def __init__(self):
            super().__init__()
            self._current_feature = None

        def enterEveryRule(self, ctx):
            name = type(ctx).__name__
            if name == "FeatureContext":
                if ctx.reference():
                    feature_name = ctx.reference().getText()
                    self._current_feature = feature_name
                    feature_type = (
                        ctx.featureType().getText() if ctx.featureType() else None
                    )
                    self.add_feature(feature_name, feature_type)
                    if ctx.featureCardinality():
                        self.mark_feature_cardinality()
            elif name == "ValueAttributeContext":
                if self._current_feature and ctx.key() and ctx.value():
                    self.add_attribute(
                        self._current_feature,
                        ctx.key().getText(),
                        ctx.value().getText(),
                    )
            elif name == "SingleConstraintAttributeContext":
                self.mark_constraint_attribute()
                self.add_feature_local_constraint(ctx.constraint().getText())
            elif name == "ListConstraintAttributeContext":
                self.mark_constraint_attribute()
                for c in ctx.constraintList().constraint():
                    self.add_feature_local_constraint(c.getText())
            elif name == "ConstraintLineContext":
                self.add_constraint(ctx.constraint().getText())

        def exitEveryRule(self, ctx):
            if type(ctx).__name__ == "FeatureContext":
                self._current_feature = None

    # ctx class name -> group kind.
    _ANTLR_GROUP_KINDS = {
        "OrGroupContext": "or",
        "AlternativeGroupContext": "xor",
        "MandatoryGroupContext": "mandatory_children",
        "OptionalGroupContext": "optional_children",
    }

    class AntlrFeatureModelBuilder(BaseFeatureModelBuilder, ParseTreeListener):
        """ANTLR-specific feature model builder."""

        def enterEveryRule(self, ctx):
            name = type(ctx).__name__
            if name == "FeatureContext":
                self._start_feature(ctx.reference().getText())
            elif name in _ANTLR_GROUP_KINDS:
                self._start_group(_ANTLR_GROUP_KINDS[name])
            elif name == "CardinalityGroupContext":
                self._start_cardinality_group(ctx.CARDINALITY().getText())

        def exitEveryRule(self, ctx):
            name = type(ctx).__name__
            if name == "FeatureContext":
                self._end_feature()
            elif name in _ANTLR_GROUP_KINDS:
                self._end_group()
            elif name == "CardinalityGroupContext":
                self._end_cardinality_group()

    _loaded = True


def parse(source):
    """Runs the ANTLR pipeline on `source`, returning (tree, extractor,
    builder).
    """
    load()
    input_stream = InputStream(source)

    lexer = uvl_custom_lexer(input_stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(CustomErrorListener())

    stream = CommonTokenStream(lexer)
    parser = uvl_python_parser(stream)
    parser.removeErrorListeners()
    parser.addErrorListener(CustomErrorListener())

    tree = parser.featureModel()

    extractor = AntlrFeatureExtractor()
    builder = AntlrFeatureModelBuilder()
    walker = ParseTreeWalker()
    walker.walk(extractor, tree)
    walker.walk(builder, tree)

    return tree, extractor, builder

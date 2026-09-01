"""Lark-backed UVL parsing: lazy import of `lark`, the Lark-specific
feature/model extraction classes, and the parse() entry point
uvllang.uvl.UVL calls for backend="lark".
"""

import os

from uvllang.feature_extraction import BaseFeatureExtractor, BaseFeatureModelBuilder
from uvllang.lark.uvl_lark_lexer import UVLIndentationLexer

_lark_mod = None


def load():
    """Lazily imports the `lark` module. Raises ImportError if lark isn't
    installed.
    """
    global _lark_mod, Tree, Token, Lark
    if _lark_mod is None:
        try:
            import lark as _lark_mod_
        except ImportError as e:
            raise ImportError(
                "Lark parser requested but lark is not installed. "
                "Install with: pip install uvllang[lark]"
            ) from e
        _lark_mod = _lark_mod_
        Tree, Token, Lark = _lark_mod.Tree, _lark_mod.Token, _lark_mod.Lark
    return _lark_mod


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
                        inner = subchild.children[0]
                        # inner.children[0] is the CONSTRAINT_KEY/
                        # CONSTRAINTS_KEY token; the constraint(s) follow.
                        if inner.data == "single_constraint_attribute":
                            self.add_feature_local_constraint(
                                _get_text(inner.children[1])
                            )
                        elif inner.data == "list_constraint_attribute":
                            constraint_list = inner.children[1]
                            for item in constraint_list.children:
                                if isinstance(item, Tree):
                                    self.add_feature_local_constraint(_get_text(item))

    def _visit_constraint_line(self, tree):
        self.add_constraint(_get_text(tree))


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
            # Not wrapped in a "groups" entry -- members stay plain
            # optional children, same as today; range/members are
            # captured separately for conversion=True.
            range_token = next(c for c in tree.children if not isinstance(c, Tree))
            self._start_cardinality_group(range_token)
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)
            self._end_cardinality_group()
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


def _get_text(tree):
    """Extract text from a Lark tree node."""
    if isinstance(tree, Token):
        return str(tree)
    elif isinstance(tree, Tree):
        return "".join(_get_text(child) for child in tree.children)
    else:
        return str(tree)


def _load_lark_parser():
    """Loads the Lark parser from grammars/uvl.lark.

    LALR, not Earley: Earley's `ambiguity="explicit"` mode was masking a
    reduce/reduce ambiguity, fixed in `constraint_atom` (grammars/uvl.lark).
    """
    grammar_path = os.path.join(
        os.path.dirname(__file__), "..", "..", "grammars", "uvl.lark"
    )

    with open(grammar_path, "r") as f:
        grammar = f.read()

    return Lark(
        grammar,
        parser="lalr",
        start="start",
        propagate_positions=True,
        maybe_placeholders=False,
    )


def parse(source):
    """Runs the Lark pipeline on `source`, returning (tree, extractor,
    builder).
    """
    load()
    lexer = UVLIndentationLexer()
    processed_content = lexer.process(source)

    parser = _load_lark_parser()
    tree = parser.parse(processed_content)

    extractor = LarkFeatureExtractor()
    builder = LarkFeatureModelBuilder()
    extractor.visit(tree)
    builder.visit(tree)

    return tree, extractor, builder

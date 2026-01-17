"""
UVL Parser using Lark

This module provides a Lark-based parser for UVL (Universal Variability Language).
It replaces the ANTLR-based parser with a pure Python Lark implementation.
"""

import os
from lark import Lark, Transformer, Tree, Token
from lark.visitors import Interpreter
from typing import List, Dict, Any, Optional


class UVLTransformer(Transformer):
    """Transformer to process the Lark parse tree into a more usable format."""

    # These methods transform the parse tree nodes
    # They are called automatically by Lark based on rule names

    def reference(self, items):
        """Combine reference parts with dots."""
        return ".".join(str(item) for item in items)

    def id(self, items):
        """Extract identifier value."""
        token = items[0]
        value = str(token)
        # Remove quotes from ID_NOT_STRICT
        if value.startswith('"') and value.endswith('"'):
            return value[1:-1]
        return value


class FeatureExtractor:
    """Extract features from the parse tree."""

    def __init__(self):
        self.features = []
        self.boolean_constraints = []
        self.arithmetic_constraints = []
        self.feature_types = {}

    def visit(self, tree):
        """Visit a tree node and extract information."""
        if not isinstance(tree, Tree):
            return

        if tree.data == "feature":
            self._visit_feature(tree)
        elif tree.data == "constraint_line":
            self._visit_constraint_line(tree)

        # Visit children
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

    def _visit_feature(self, tree):
        """Extract feature name when visiting a feature node."""
        for child in tree.children:
            if isinstance(child, Tree) and child.data == "reference":
                feature_name = self._get_text(child)
                self.features.append(feature_name)

                # Check for feature type
                for sibling in tree.children:
                    if isinstance(sibling, Tree) and sibling.data == "feature_type":
                        type_text = self._get_text(sibling)
                        self.feature_types[feature_name] = type_text
                break

    def _visit_constraint_line(self, tree):
        """Extract constraints from constraint_line nodes."""
        constraint_text = self._get_text(tree)

        # Check if this is an arithmetic constraint (has comparison operators)
        # Note: We must check for boolean operators first to avoid false matches
        # (e.g., ">=" matches within "=>" or "<=>" matches within "<=")
        has_boolean_op = any(op in constraint_text for op in ["=>", "<=>"])
        has_arithmetic_op = any(
            op in constraint_text for op in ["==", "!=", "<=", ">=", "<", ">"]
        )

        if has_arithmetic_op and not has_boolean_op:
            self.arithmetic_constraints.append(constraint_text)
        else:
            self.boolean_constraints.append(constraint_text)

    def _get_text(self, tree):
        """Get the text content of a tree node."""
        if isinstance(tree, Token):
            return str(tree)
        elif isinstance(tree, Tree):
            return "".join(self._get_text(child) for child in tree.children)
        else:
            return str(tree)


class FeatureModelBuilder:
    """Build feature model hierarchy from parse tree."""

    def __init__(self):
        self.root_feature = None
        self.feature_hierarchy = {}
        self.current_feature = None
        self.feature_stack = []
        self.current_group = None
        self.group_stack = []

    def visit(self, tree):
        """Visit a tree node and build hierarchy."""
        if not isinstance(tree, Tree):
            return

        # Dispatch based on node type
        if tree.data == "feature":
            self._visit_feature(tree)
        elif tree.data == "or_group":
            self._visit_or_group(tree)
        elif tree.data == "alternative_group":
            self._visit_alternative_group(tree)
        elif tree.data == "optional_group":
            self._visit_optional_group(tree)
        elif tree.data == "mandatory_group":
            self._visit_mandatory_group(tree)
        else:
            # Visit children for other node types
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)

    def _visit_feature(self, tree):
        """Process a feature node."""
        feature_name = None

        # Extract feature name from reference
        for child in tree.children:
            if isinstance(child, Tree) and child.data == "reference":
                feature_name = self._get_text(child)
                break

        if not feature_name:
            # Visit children anyway
            for child in tree.children:
                if isinstance(child, Tree):
                    self.visit(child)
            return

        # Set root feature if not set
        if self.root_feature is None:
            self.root_feature = feature_name

        # Initialize feature in hierarchy
        if feature_name not in self.feature_hierarchy:
            self.feature_hierarchy[feature_name] = {
                "parent": self.current_feature,
                "children": [],
                "groups": [],
            }

        # Determine child type based on current group
        child_type = "optional"
        if self.current_group and self.current_group[0] == "mandatory":
            child_type = "mandatory"

        # Add to current group if in a group
        if self.current_group:
            self.current_group[1].append(feature_name)

        # Add as child to parent
        if self.current_feature:
            self.feature_hierarchy[self.current_feature]["children"].append(
                (feature_name, child_type)
            )

        # Update current feature context
        self.feature_stack.append(self.current_feature)
        self.current_feature = feature_name

        # Visit children (nested features, groups, etc.)
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        # Restore previous feature context
        self.current_feature = self.feature_stack.pop() if self.feature_stack else None

    def _visit_or_group(self, tree):
        """Process an OR group."""
        if self.current_feature:
            self.current_group = ("or", [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]["groups"].append(
                self.current_group
            )

        # Visit children
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        if self.group_stack:
            self.group_stack.pop()
            self.current_group = self.group_stack[-1] if self.group_stack else None

    def _visit_alternative_group(self, tree):
        """Process an alternative (XOR) group."""
        if self.current_feature:
            self.current_group = ("xor", [])
            self.group_stack.append(self.current_group)
            self.feature_hierarchy[self.current_feature]["groups"].append(
                self.current_group
            )

        # Visit children
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        if self.group_stack:
            self.group_stack.pop()
            self.current_group = self.group_stack[-1] if self.group_stack else None

    def _visit_optional_group(self, tree):
        """Process an optional group."""
        if self.current_feature:
            self.current_group = ("optional_children", [])
            self.group_stack.append(self.current_group)

        # Visit children
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        if self.group_stack:
            self.group_stack.pop()
            self.current_group = self.group_stack[-1] if self.group_stack else None

    def _visit_mandatory_group(self, tree):
        """Process a mandatory group."""
        if self.current_feature:
            self.current_group = ("mandatory", [])
            self.group_stack.append(self.current_group)

        # Visit children
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)

        if self.group_stack:
            self.group_stack.pop()
            self.current_group = self.group_stack[-1] if self.group_stack else None

    def _get_text(self, tree):
        """Get the text content of a tree node."""
        if isinstance(tree, Token):
            return str(tree)
        elif isinstance(tree, Tree):
            return "".join(self._get_text(child) for child in tree.children)
        else:
            return str(tree)


def load_lark_parser() -> Lark:
    """Load the Lark parser from the grammar file."""
    grammar_path = os.path.join(os.path.dirname(__file__), "..", "grammars", "uvl.lark")

    with open(grammar_path, "r") as f:
        grammar = f.read()

    # Create Lark parser with Earley algorithm (handles ambiguity better)
    parser = Lark(
        grammar,
        parser="earley",
        start="start",
        propagate_positions=True,
        maybe_placeholders=False,
        ambiguity="explicit",  # Handle ambiguity explicitly
    )

    return parser

"""Shared extraction scaffolding for the Lark and ANTLR backends: base
classes each backend's grammar-specific extractor/builder subclasses
(uvllang/lark/uvl_lark_parser.py, uvllang/antlr4/uvl_antlr_parser.py),
plus the couple of helpers both share. Nothing here is UVL-specific (the
zig backend never touches this module) or grammar-specific (neither Lark
nor ANTLR owns it).
"""


class BaseFeatureExtractor:
    """Base class for feature and constraint extraction."""

    def __init__(self):
        self.features = []
        self.boolean_constraints = []
        self.arithmetic_constraints = []
        self.feature_types = {}
        self.feature_attributes = {}  # {feature: {attr_name: value}}
        # Tier 1 counts (docs/non_boolean_support.md).
        self.cardinality_feature_count = 0
        self.constraint_attribute_count = 0
        # Raw text of every feature-local `constraint`/`constraints`
        # attribute -- used only when conversion=True (see
        # BaseFeatureModelBuilder.cardinality_groups for the analogous
        # group-cardinality state).
        self.feature_local_constraint_texts = []

    def add_feature(self, feature_name, feature_type=None):
        self.features.append(feature_name)
        if feature_type:
            self.feature_types[feature_name] = feature_type

    def mark_feature_cardinality(self):
        """A feature declares a clone cardinality ([i..j]) -- Tier 1."""
        self.cardinality_feature_count += 1

    def mark_constraint_attribute(self):
        """A feature-local `{constraint ...}`/`{constraints [...]}`
        attribute was seen and dropped -- Tier 1.
        """
        self.constraint_attribute_count += 1

    def add_feature_local_constraint(self, constraint_text):
        self.feature_local_constraint_texts.append(constraint_text)

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
    """True if `constraint_text` is a bare comparison, not
    boolean-encodable.
    """
    has_boolean_op = any(op in constraint_text for op in ["=>", "<=>"])
    has_arithmetic_op = any(
        op in constraint_text for op in ["==", "!=", "<=", ">=", "<", ">"]
    )
    return has_arithmetic_op and not has_boolean_op


def _parse_cardinality_range(text):
    """Parses a `[min..max]`/`[min..*]`/`[n]` cardinality token into
    `(min, max_or_None)`. Mirrors parser.zig's parseCardinalityRange.
    """
    inner = text[1:-1]
    if ".." in inner:
        min_s, max_s = inner.split("..", 1)
        min_ = int(min_s)
        return min_, (None if max_s == "*" else int(max_s))
    n = int(inner)
    return n, n


class BaseFeatureModelBuilder:
    """Base class for building feature model hierarchy."""

    def __init__(self):
        self.root_feature = None
        self.feature_hierarchy = {}
        self.current_feature = None
        self.feature_stack = []
        self.current_group = None
        self.group_stack = []
        # Tier 1 (docs/non_boolean_support.md).
        self.cardinality_group_count = 0
        # [(parent, min, max_or_None, [member, ...]), ...] -- used only
        # when conversion=True (see uvllang._zig.hierarchy_to_cnf).
        self.cardinality_groups = []
        self._cardinality_stack = []

    def mark_cardinality_group(self):
        self.cardinality_group_count += 1

    def _start_cardinality_group(self, range_text):
        self.mark_cardinality_group()
        min_, max_ = _parse_cardinality_range(range_text)
        before = len(self.feature_hierarchy[self.current_feature]["children"])
        self._cardinality_stack.append((self.current_feature, min_, max_, before))

    def _end_cardinality_group(self):
        parent, min_, max_, before = self._cardinality_stack.pop()
        members = [
            name for name, _ in self.feature_hierarchy[parent]["children"][before:]
        ]
        self.cardinality_groups.append((parent, min_, max_, members))

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

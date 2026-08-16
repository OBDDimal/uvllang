pub const Kind = enum {
    eof,
    newline,
    indent,
    dedent,

    // keywords
    include_key,
    features_key,
    imports_key,
    namespace_key,
    as_key,
    constraint_key,
    constraints_key,
    cardinality_key,
    string_key,
    boolean_key,
    integer_key,
    real_key,
    len_key,
    sum_key,
    avg_key,
    floor_key,
    ceil_key,
    arithmetic_key,
    group_cardinality_key,
    feature_cardinality_key,
    aggregate_key,
    string_constraints_key,

    or_group,
    alternative,
    optional,
    mandatory,

    cardinality_lit, // [n..m] / [n..*] / [n]

    // operators
    not,
    amp,
    pipe,
    equivalence,
    implication,
    eq,
    lt,
    le,
    gt,
    ge,
    ne,
    div,
    mul,
    add,
    sub,

    lparen,
    rparen,
    lbrack,
    rbrack,
    lbrace,
    rbrace,

    float,
    integer,
    boolean_lit,

    comma,
    dot,

    id_not_strict,
    id_strict,
    string_lit,
};

pub const Token = struct {
    kind: Kind,
    text: []const u8,
    line: u32,
};

pub const KeywordEntry = struct {
    text: []const u8,
    kind: Kind,
    alpha: bool,
};

// Sorted longest-first so a linear scan picks the longest valid match.
pub const literal_table = blk: {
    @setEvalBranchQuota(4000);
    const raw = [_]KeywordEntry{
        .{ .text = "group-cardinality", .kind = .group_cardinality_key, .alpha = true },
        .{ .text = "feature-cardinality", .kind = .feature_cardinality_key, .alpha = true },
        .{ .text = "aggregate-function", .kind = .aggregate_key, .alpha = true },
        .{ .text = "string-constraints", .kind = .string_constraints_key, .alpha = true },
        .{ .text = "constraints", .kind = .constraints_key, .alpha = true },
        .{ .text = "constraint", .kind = .constraint_key, .alpha = true },
        .{ .text = "cardinality", .kind = .cardinality_key, .alpha = true },
        .{ .text = "namespace", .kind = .namespace_key, .alpha = true },
        .{ .text = "alternative", .kind = .alternative, .alpha = true },
        .{ .text = "Arithmetic", .kind = .arithmetic_key, .alpha = true },
        .{ .text = "mandatory", .kind = .mandatory, .alpha = true },
        .{ .text = "features", .kind = .features_key, .alpha = true },
        .{ .text = "Boolean", .kind = .boolean_key, .alpha = true },
        .{ .text = "Integer", .kind = .integer_key, .alpha = true },
        .{ .text = "imports", .kind = .imports_key, .alpha = true },
        .{ .text = "include", .kind = .include_key, .alpha = true },
        .{ .text = "optional", .kind = .optional, .alpha = true },
        .{ .text = "String", .kind = .string_key, .alpha = true },
        .{ .text = "floor", .kind = .floor_key, .alpha = true },
        .{ .text = "false", .kind = .boolean_lit, .alpha = true },
        .{ .text = "Real", .kind = .real_key, .alpha = true },
        .{ .text = "true", .kind = .boolean_lit, .alpha = true },
        .{ .text = "ceil", .kind = .ceil_key, .alpha = true },
        .{ .text = "avg", .kind = .avg_key, .alpha = true },
        .{ .text = "sum", .kind = .sum_key, .alpha = true },
        .{ .text = "len", .kind = .len_key, .alpha = true },
        .{ .text = "as", .kind = .as_key, .alpha = true },
        .{ .text = "or", .kind = .or_group, .alpha = true },

        .{ .text = "<=>", .kind = .equivalence, .alpha = false },
        .{ .text = "==", .kind = .eq, .alpha = false },
        .{ .text = "<=", .kind = .le, .alpha = false },
        .{ .text = ">=", .kind = .ge, .alpha = false },
        .{ .text = "!=", .kind = .ne, .alpha = false },
        .{ .text = "=>", .kind = .implication, .alpha = false },
        .{ .text = "!", .kind = .not, .alpha = false },
        .{ .text = "&", .kind = .amp, .alpha = false },
        .{ .text = "|", .kind = .pipe, .alpha = false },
        .{ .text = "<", .kind = .lt, .alpha = false },
        .{ .text = ">", .kind = .gt, .alpha = false },
        .{ .text = "(", .kind = .lparen, .alpha = false },
        .{ .text = ")", .kind = .rparen, .alpha = false },
        .{ .text = "[", .kind = .lbrack, .alpha = false },
        .{ .text = "]", .kind = .rbrack, .alpha = false },
        .{ .text = "{", .kind = .lbrace, .alpha = false },
        .{ .text = "}", .kind = .rbrace, .alpha = false },
        .{ .text = ",", .kind = .comma, .alpha = false },
        .{ .text = ".", .kind = .dot, .alpha = false },
        .{ .text = "/", .kind = .div, .alpha = false },
        .{ .text = "*", .kind = .mul, .alpha = false },
        .{ .text = "+", .kind = .add, .alpha = false },
        .{ .text = "-", .kind = .sub, .alpha = false },
    };

    // Bubble sort by descending text length (comptime, small array).
    var arr = raw;
    var i: usize = 0;
    while (i < arr.len) : (i += 1) {
        var j: usize = 0;
        while (j < arr.len - 1 - i) : (j += 1) {
            if (arr[j].text.len < arr[j + 1].text.len) {
                const tmp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = tmp;
            }
        }
    }
    break :blk arr;
};

"""
Custom Lark Lexer for UVL with Indentation Support

This lexer preprocesses the input to insert INDENT and DEDENT tokens
based on indentation levels, similar to Python's indentation handling.

This is a single-pass character scanner rather than a line-split-and-patch
preprocessor, deliberately mirroring uvllang/uvl_custom_lexer.py's
(ANTLR's) actual approach: real state (bracket depth, whether we're inside
a quoted literal) carried across the whole scan, comments and indentation
resolved together instead of as separate passes that can't see each
other's context. A line-based preprocessor structurally cannot get this
right -- it has to guess line-by-line whether a given line is "real"
without knowing whether an unclosed string or block comment from a
previous line is still open, or whether a `//`/`/*` inside a quoted
literal (e.g. a URL in a string attribute value) should count as a real
comment. Scanning once, left to right, with the same state ANTLR's lexer
tracks, makes those questions have an actual, unambiguous answer instead
of a per-case patch.

Where the two grammars' literal definitions differ, this follows ANTLR's
-- ANTLR is effectively the reference `uvl_custom_lexer.py` companion this
was built to match, and this project verifies both backends against it.
The one deliberate case: block comments are matched greedily (through to
the *last* "*/" in the remaining text), matching uvl_lexer.g4's
`OPEN_COMMENT .* CLOSE_COMMENT` (ANTLR4's `.*` is greedy by default) --
even though the standalone `grammars/uvl.lark` file's own COMMENT
terminal is written non-greedy (`.*?`). Indentation uses the same
tab-stop-8 rule as ANTLR's `getIndentationCount`, not a flat tab=4.
"""

def _indent_width(spaces: str) -> int:
    """Tab-stop-8, matching uvl_custom_lexer.py's getIndentationCount."""
    count = 0
    for ch in spaces:
        if ch == "\t":
            count += 8 - (count % 8)
        else:
            count += 1
    return count


class UVLIndentationLexer:
    """Preprocessor that adds INDENT/DEDENT tokens based on indentation."""

    def __init__(self):
        self.indent_stack = [0]

    def process(self, text: str) -> str:
        """
        Scans `text` once, left to right, and returns it with <INDENT> and
        <DEDENT> markers inserted and all comments removed. Quoted string
        and identifier literals (`"..."` / `'...'`) are copied through
        verbatim so a `//` or `/*` inside one is never mistaken for a
        comment. Newlines inside an open `(`/`[`/`{` don't affect
        indentation, matching the grammar's own bracket-depth tracking.
        """
        n = len(text)
        out = []
        i = 0
        opened = 0
        started = False  # has any real (non-comment, non-blank) token been emitted yet

        def skip_line_comment(i):
            end = text.find("\n", i)
            return n if end == -1 else end

        def skip_quoted(i, quote):
            end = i + 1
            while end < n and text[end] not in (quote, "\n", "\r"):
                end += 1
            return end + 1 if end < n and text[end] == quote else end

        def skip_block_comment(i):
            # Greedy: match through to the LAST "*/" anywhere in the
            # remaining text, matching uvl_lexer.g4's `OPEN_COMMENT .*
            # CLOSE_COMMENT` (ANTLR4's `.*` is greedy by default).
            #
            # This is deliberately *not* quote-aware, even though a "*/"
            # inside some later, unrelated quoted string can then end up
            # closing this comment early (verified empirically: ANTLR's
            # own generated lexer does exactly this too, since once it
            # commits to the COMMENT rule it's matching via that rule's
            # own `.*` against raw characters, never re-entering the
            # STRING/ID_NOT_STRICT rules to recognize a quote boundary
            # partway through). Making this smarter than ANTLR would trade
            # one bug for a silent behavioral mismatch between the two
            # backends, which is worse.
            last_close = text.rfind("*/", i + 2)
            return last_close + 2 if last_close != -1 else n  # unterminated: consume to EOF

        while i < n:
            c = text[i]

            if text[i : i + 2] == "//":
                i = skip_line_comment(i)
                continue
            if text[i : i + 2] == "/*":
                i = skip_block_comment(i)
                continue

            if c == '"' or c == "'":
                end = skip_quoted(i, c)
                out.append(text[i:end])
                started = True
                i = end
                continue

            if c in "([{":
                opened += 1
                out.append(c)
                started = True
                i += 1
                continue
            if c in ")]}":
                opened -= 1
                out.append(c)
                started = True
                i += 1
                continue

            if c == "\r" or c == "\n":
                i += 2 if c == "\r" and i + 1 < n and text[i + 1] == "\n" else 1

                if opened > 0:
                    continue  # insignificant inside brackets

                j = i
                while j < n and text[j] in " \t":
                    j += 1
                spaces = text[i:j]

                # Blank line, or a line whose first non-whitespace content
                # is a comment: carries no indentation information, skip
                # entirely (don't even emit the newline) rather than let
                # its unrelated leading whitespace be read as a real
                # indent change.
                if j >= n or text[j] in "\r\n" or text[j : j + 2] in ("//", "/*"):
                    i = j
                    continue

                i = j

                if not started:
                    # A leading blank/comment run before the first real
                    # token: the grammar's `namespace? NEWLINE? includes?
                    # NEWLINE? ...` has no NEWLINE slot before namespace
                    # itself, so this newline has nowhere to go.
                    continue

                indent = _indent_width(spaces)
                previous = self.indent_stack[-1]
                if indent == previous:
                    out.append("\n")
                elif indent > previous:
                    self.indent_stack.append(indent)
                    out.append("\n<INDENT> ")
                else:
                    out.append("\n")
                    while len(self.indent_stack) > 1 and self.indent_stack[-1] > indent:
                        self.indent_stack.pop()
                        out.append("<DEDENT> ")
                continue

            out.append(c)
            if not c.isspace():
                started = True
            i += 1

        if len(self.indent_stack) > 1:
            out.append("\n")
            while len(self.indent_stack) > 1:
                self.indent_stack.pop()
                out.append("<DEDENT> ")

        return "".join(out)

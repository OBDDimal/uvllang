"""
Custom Lark Lexer for UVL with Indentation Support

This lexer preprocesses the input to insert INDENT and DEDENT tokens
based on indentation levels, similar to Python's indentation handling.
"""

from lark import Token
from typing import List, Iterator


class UVLIndentationLexer:
    """Preprocessor that adds INDENT/DEDENT tokens based on indentation."""

    def __init__(self):
        self.indent_stack = [0]

    def process(self, text: str) -> str:
        """
        Process the input text and insert <INDENT> and <DEDENT> tokens.

        Args:
            text: Raw UVL text input

        Returns:
            Processed text with INDENT/DEDENT tokens inline
        """
        lines = text.split("\n")
        output_lines = []

        for i, line in enumerate(lines):
            # Skip empty lines (don't add them to output)
            if not line.strip():
                continue

            # Calculate indentation level (tabs counted as 4 spaces)
            indent_level = 0
            for char in line:
                if char == "\t":
                    indent_level += 4
                elif char == " ":
                    indent_level += 1
                else:
                    break

            # Get the content without leading whitespace
            content = line.lstrip()

            # Handle indentation changes
            current_indent = self.indent_stack[-1]

            if indent_level > current_indent:
                # INDENT - insert token before content on same line
                self.indent_stack.append(indent_level)
                output_lines.append(f"<INDENT> {content}")
            elif indent_level < current_indent:
                # DEDENT (possibly multiple levels)
                dedent_tokens = []
                while self.indent_stack and self.indent_stack[-1] > indent_level:
                    self.indent_stack.pop()
                    dedent_tokens.append("<DEDENT>")

                # Add DEDENT tokens before content on same line
                output_lines.append(
                    f'{" ".join(dedent_tokens)} {content}' if dedent_tokens else content
                )
            else:
                # Same indentation level
                output_lines.append(content)

        # Add final DEDENTs at end
        dedent_tokens = []
        while len(self.indent_stack) > 1:
            self.indent_stack.pop()
            dedent_tokens.append("<DEDENT>")

        if dedent_tokens:
            output_lines.append(" ".join(dedent_tokens))

        return "\n".join(output_lines)

"""Lark backend support: uvl_lark_lexer.py is the indentation
(INDENT/DEDENT) preprocessor fed to the Lark grammar (grammars/uvl.lark)
before parsing, mirroring uvllang/antlr4/uvl_custom_lexer.py's approach
for the ANTLR backend. uvl_lark_parser.py wires it together with the
grammar and the feature/model extraction classes, exposing parse() to
uvllang.uvl.UVL.
"""

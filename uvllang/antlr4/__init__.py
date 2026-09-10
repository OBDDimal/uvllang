"""ANTLR4 backend support.

uvl_python_lexer.py, uvl_python_parser.py, and uvl_python_parser_listener.py
are generated output (grammars/uvl_python_lexer.g4,
grammars/uvl_python_parser.g4, produced by generate_parsers.py -- do not
hand-edit them). Two hand-written modules sit alongside them:
uvl_custom_lexer.py subclasses the generated uvl_python_lexer to add
indentation (INDENT/DEDENT) handling ANTLR's own lexer generator can't
express; uvl_antlr_parser.py wires it together with the generated parser
and the feature/model extraction classes, exposing parse() to
uvllang.uvl.UVL.
"""

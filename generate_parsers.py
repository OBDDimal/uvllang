#!/usr/bin/env python3
"""
Script to generate Python parsers from ANTLR4 grammars.
"""

import subprocess
import sys
from pathlib import Path

def generate_parsers():
    """Generate the Python parsers from ANTLR4 grammars."""
    repo_root = Path(__file__).parent
    grammars_dir = repo_root / "grammars"
    uvl_dir = repo_root / "uvl"

    # ANTLR4 command - run from grammars directory
    cmd = [
        "antlr4",
        "-Dlanguage=Python3",
        "-o", ".",
        "uvl_python_lexer.g4",
        "uvl_python_parser.g4"
    ]

    print("Generating parsers...")
    print("cd grammars && " + " ".join(cmd))

    try:
        result = subprocess.run(cmd, cwd=grammars_dir, check=True)
        print("Parsers generated successfully!")
    except subprocess.CalledProcessError as e:
        print(f"Error generating parsers: {e}")
        return 1
    except FileNotFoundError:
        print("antlr4 command not found. Please install antlr4-tools.")
        return 1

    # Move generated .py files to uvl directory
    generated_files = list(grammars_dir.glob("*.py"))
    for file in generated_files:
        # Rename files to snake_case
        if file.name == "uvl_python_parserListener.py":
            new_name = "uvl_python_parser_listener.py"
        else:
            new_name = file.name
        
        dest = uvl_dir / new_name
        file.rename(dest)
        print(f"Moved {file.name} to uvl/{new_name}")

    # Clean up ANTLR4 artifacts
    for pattern in ["*.tokens", "*.interp"]:
        for artifact_file in grammars_dir.glob(pattern):
            artifact_file.unlink()
            print(f"Cleaned up {artifact_file.name}")

    return 0

if __name__ == "__main__":
    sys.exit(generate_parsers())
#!/usr/bin/env python3
"""
Build script that generates parsers and builds the package.
"""

import subprocess
import sys
import os

def main():
    """Generate parsers and build the package."""

    # Change to the script's directory
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)

    print("Generating ANTLR parsers...")
    result = subprocess.run([sys.executable, "generate_parsers.py"],
                          capture_output=True, text=True)

    if result.returncode != 0:
        print("X Parser generation failed:")
        print(result.stderr)
        return result.returncode

    print("Parsers generated successfully")
    print(result.stdout.strip())

    print("\nBuilding package...")
    result = subprocess.run([sys.executable, "-m", "build"],
                          capture_output=True, text=True)

    if result.returncode != 0:
        print("X Package build failed:")
        print(result.stderr)
        return result.returncode

    print("Package built successfully")
    print(result.stdout.strip())

    return 0

if __name__ == "__main__":
    sys.exit(main())
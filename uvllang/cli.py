#!/usr/bin/env python3
"""
CLI tool for converting UVL files to CNF/DIMACS format.
"""

import sys
import os
from uvllang.main import UVL


def main():
    if len(sys.argv) < 2:
        print("Usage: uvl2cnf <uvl_file> [output_file]")
        print("\nConvert a UVL feature model to CNF in DIMACS format.")
        print("\nArguments:")
        print("  uvl_file     Path to the input UVL file")
        print("  output_file  Optional path to output DIMACS file")
        print("               (default: <uvl_filename>.dimacs in current directory)")
        sys.exit(1)

    uvl_file = sys.argv[1]
    
    if not os.path.exists(uvl_file):
        print(f"Error: File '{uvl_file}' not found")
        sys.exit(1)

    if len(sys.argv) > 2:
        output_file = sys.argv[2]
    else:
        basename = os.path.basename(uvl_file)
        output_file = os.path.splitext(basename)[0] + '.dimacs'

    try:
        model = UVL(from_file=uvl_file)
        cnf = model.to_cnf()

        with open(output_file, 'w') as f:
            f.write(f"p cnf {len(model.features)} {len(cnf)}\n")
            for clause in cnf:
                f.write(' '.join(map(str, clause)) + ' 0\n')

        print(f"Saved DIMACS to {output_file}")

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
CLI tool for converting UVL files to CNF/DIMACS format.
"""

import sys
import os
import argparse
from uvllang.main import UVL


def main():
    parser = argparse.ArgumentParser(
        description="Convert a UVL feature model to CNF in DIMACS format.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  uvl2cnf model.uvl                    # Convert to model.dimacs
  uvl2cnf model.uvl output.dimacs      # Convert to specific output file
  uvl2cnf model.uvl -v                 # Verbose output showing ignored constraints
        """
    )
    
    parser.add_argument('uvl_file', help='Path to the input UVL file')
    parser.add_argument('output_file', nargs='?', help='Optional path to output DIMACS file (default: <uvl_filename>.dimacs)')
    parser.add_argument('-v', '--verbose', action='store_true', help='Show detailed information about ignored constraints and types')
    
    args = parser.parse_args()
    
    uvl_file = args.uvl_file
    
    if not os.path.exists(uvl_file):
        print(f"Error: File '{uvl_file}' not found")
        sys.exit(1)

    if args.output_file:
        output_file = args.output_file
    else:
        basename = os.path.basename(uvl_file)
        output_file = os.path.splitext(basename)[0] + '.dimacs'

    try:
        model = UVL(from_file=uvl_file)
        
        if args.verbose:
            if model.arithmetic_constraints:
                print(f"Info: Ignored {len(model.arithmetic_constraints)} arithmetic constraints")
                for i, constraint in enumerate(model.arithmetic_constraints[:10], 1):  # Show first 10
                    print(f"  {i}. {constraint}")
                if len(model.arithmetic_constraints) > 10:
                    print(f"  ... and {len(model.arithmetic_constraints) - 10} more")
            if model.feature_types:
                print(f"Info: Ignored {len(model.feature_types)} feature type declarations")
                for feature, ftype in list(model.feature_types.items())[:10]:  # Show first 10
                    print(f"  {feature}: {ftype}")
                if len(model.feature_types) > 10:
                    print(f"  ... and {len(model.feature_types) - 10} more")
        
        cnf = model.to_cnf(verbose_info=not args.verbose)

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

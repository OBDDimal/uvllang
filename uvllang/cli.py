#!/usr/bin/env python3
"""
CLI tool for converting UVL files to CNF/DIMACS format.
"""

import sys
import os
import argparse
from uvllang.main import UVL


def uvl2cnf():
    parser = argparse.ArgumentParser(
        description="Convert a UVL feature model to CNF in DIMACS format.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  uvl2cnf model.uvl                    # Convert to model.dimacs (using Lark)
  uvl2cnf model.uvl output.dimacs      # Convert to specific output file
  uvl2cnf model.uvl -v                 # Verbose output showing ignored constraints
  uvl2cnf model.uvl --antlr            # Use ANTLR parser instead of Lark
        """,
    )

    parser.add_argument("uvl_file", help="Path to the input UVL file")
    parser.add_argument(
        "output_file",
        nargs="?",
        help="Optional path to output DIMACS file (default: <uvl_filename>.dimacs)",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Show detailed information about ignored constraints and types",
    )
    parser.add_argument(
        "--lark",
        action="store_true",
        help="Use Lark parser (default)",
    )
    parser.add_argument(
        "--antlr",
        action="store_true",
        help="Use ANTLR parser instead of Lark",
    )

    args = parser.parse_args()

    # Determine which parser to use (Lark is default)
    use_antlr = args.antlr

    if args.verbose:
        print(f"Using {'ANTLR' if use_antlr else 'Lark'} parser")

    uvl_file = args.uvl_file

    if not os.path.exists(uvl_file):
        print(f"Error: File '{uvl_file}' not found")
        sys.exit(1)

    if args.output_file:
        output_file = args.output_file
    else:
        basename = os.path.basename(uvl_file)
        output_file = os.path.splitext(basename)[0] + ".dimacs"

    try:
        model = UVL(from_file=uvl_file, use_antlr=use_antlr)

        if args.verbose:
            if model.arithmetic_constraints:
                print(
                    f"Info: Ignored {len(model.arithmetic_constraints)} arithmetic constraints"
                )
                for i, constraint in enumerate(
                    model.arithmetic_constraints[:10], 1
                ):  # Show first 10
                    print(f"  {i}. {constraint.strip()}")
                if len(model.arithmetic_constraints) > 10:
                    print(f"  ... and {len(model.arithmetic_constraints) - 10} more")
            if model.feature_types:
                print(
                    f"Info: Ignored {len(model.feature_types)} feature type declarations"
                )
                for feature, ftype in list(model.feature_types.items())[
                    :10
                ]:  # Show first 10
                    print(f"  {feature}: {ftype}")
                if len(model.feature_types) > 10:
                    print(f"  ... and {len(model.feature_types) - 10} more")

        cnf_formula = model.to_cnf(verbose_info=not args.verbose)
        cnf_formula.to_file(output_file)

        print(f"Saved DIMACS to {output_file}")

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


def uvl2smt():
    """CLI tool for converting UVL files to SMT-LIB 2 format."""
    parser = argparse.ArgumentParser(
        description="Convert a UVL feature model to SMT-LIB 2 format.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  uvl2smt model.uvl                    # Convert to model.smt2 (using Lark)
  uvl2smt model.uvl output.smt2        # Convert to specific output file
  uvl2smt model.uvl -v                 # Verbose output
  uvl2smt model.uvl --antlr            # Use ANTLR parser instead of Lark
        """,
    )

    parser.add_argument("uvl_file", help="Path to the input UVL file")
    parser.add_argument(
        "output_file",
        nargs="?",
        help="Optional path to output SMT-LIB 2 file (default: <uvl_filename>.smt2)",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Show detailed information about the model",
    )
    parser.add_argument(
        "--lark",
        action="store_true",
        help="Use Lark parser (default)",
    )
    parser.add_argument(
        "--antlr",
        action="store_true",
        help="Use ANTLR parser instead of Lark",
    )

    args = parser.parse_args()

    use_antlr = args.antlr

    if args.verbose:
        print(f"Using {'ANTLR' if use_antlr else 'Lark'} parser")

    uvl_file = args.uvl_file

    if not os.path.exists(uvl_file):
        print(f"Error: File '{uvl_file}' not found")
        sys.exit(1)

    if args.output_file:
        output_file = args.output_file
    else:
        basename = os.path.basename(uvl_file)
        output_file = os.path.splitext(basename)[0] + ".smt2"

    try:
        model = UVL(from_file=uvl_file, use_antlr=use_antlr)
        smt_content = model.to_smt()

        with open(output_file, "w") as f:
            f.write(smt_content)

        print(f"Successfully converted UVL model to SMT-LIB 2 format: {output_file}")

        if args.verbose:
            print(f"Features: {len(model.features)}")
            print(f"Boolean constraints: {len(model.boolean_constraints)}")
            print(f"Arithmetic constraints: {len(model.arithmetic_constraints)}")
            if model.feature_attributes:
                print(f"Features with attributes: {len(model.feature_attributes)}")
            if model.feature_types:
                print(f"Typed features: {len(model.feature_types)}")

    except Exception as e:
        print(f"Error: {e}")
        if args.verbose:
            import traceback

            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    uvl2cnf()

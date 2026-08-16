#!/usr/bin/env python3
"""
CLI tool for converting UVL files to CNF/SMT format.
"""

import sys
import os
import argparse
from uvllang.main import UVL
from uvllang import _zig
from pysat.formula import CNF


def uvl2cnf():
    parser = argparse.ArgumentParser(
        description="Convert a UVL feature model to CNF in DIMACS format.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  uvl2cnf model.uvl                    # Convert to model.dimacs (Zig lexes, parses, and builds the CNF)
  uvl2cnf model.uvl output.dimacs      # Convert to specific output file
  uvl2cnf model.uvl -v                 # Verbose output showing ignored constraints
  uvl2cnf model.uvl --antlr            # Parse with ANTLR, hand off to Zig for CNF generation
  uvl2cnf model.uvl --lark             # Parse with Lark, hand off to Zig for CNF generation

By default (no --antlr/--lark), parsing and CNF generation both happen in
the Zig backend; Python doesn't parse the file at all. Any ignored
constraint/type info in that mode is printed by Zig directly, regardless
of -v.
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
        "--antlr",
        action="store_true",
        help="Parse with ANTLR, hand off to Zig for CNF generation",
    )
    parser.add_argument(
        "--lark",
        action="store_true",
        help="Parse with Lark, hand off to Zig for CNF generation",
    )

    args = parser.parse_args()

    if args.antlr and args.lark:
        print("Error: --antlr and --lark are mutually exclusive")
        sys.exit(1)

    if args.verbose:
        if args.antlr:
            print("Using ANTLR parser (Zig backend for CNF generation)")
        elif args.lark:
            print("Using Lark parser (Zig backend for CNF generation)")
        else:
            print("Using Zig for parsing and CNF generation")

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
        if args.antlr or args.lark:
            model = UVL(from_file=uvl_file, use_antlr=args.antlr)

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
        else:
            with open(uvl_file, "r", encoding="utf-8") as f:
                source = f.read()
            clauses, id_to_name = _zig.parse_source_to_cnf(source)
            cnf_formula = CNF(from_clauses=clauses)
            cnf_formula.comments = [
                f"c {ident} {name}" for ident, name in sorted(id_to_name.items())
            ]

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


def any2uvl():
    """CLI tool for converting CNF/DIMACS files to UVL format."""
    parser = argparse.ArgumentParser(
        description="Convert a DIMACS CNF file to UVL format.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  any2uvl model.dimacs                 # Convert to model_recovered.uvl
  any2uvl model.dimacs output.uvl      # Convert to specific output file
  any2uvl --optimize model.dimacs      # Run CTC-reduction optimiser after recovery
        """,
    )

    parser.add_argument("input_file", help="Path to the input CNF/DIMACS file")
    parser.add_argument(
        "output_file",
        nargs="?",
        help="Optional path to output UVL file (default: <input_filename>_recovered.uvl)",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Show detailed information about the conversion",
    )
    parser.add_argument(
        "--optimize",
        action="store_true",
        help="Run CTC-reduction postprocessing after recovery",
    )
    parser.add_argument(
        "--byname",
        action="store_true",
        help="Break parent-assignment ties by feature name similarity",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="After --optimize, reparse the written file and check it's still equivalent to the input DIMACS",
    )

    args = parser.parse_args()

    input_file = args.input_file

    if not os.path.exists(input_file):
        print(f"Error: File '{input_file}' not found")
        sys.exit(1)

    if args.output_file:
        output_file = args.output_file
    else:
        basename = os.path.basename(input_file)
        name_without_ext = os.path.splitext(basename)[0]
        output_file = name_without_ext + "_recovered.uvl"

    try:
        if args.verbose:
            print(f"Converting {input_file} to UVL format...")

        UVL.from_cnf(input_file, output_file, optimize=args.optimize, by_name=args.byname, verify=args.verify)

        print(f"Successfully converted to UVL format: {output_file}")

    except Exception as e:
        print(f"Error: {e}")
        if args.verbose:
            import traceback

            traceback.print_exc()
        sys.exit(1)

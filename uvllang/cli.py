#!/usr/bin/env python3
"""
CLI tools for converting UVL files to SMT format and DIMACS back to UVL.

uvl2cnf and uvl2uvl are NOT here: they're pure native binaries
(parser/zig-out/bin/{uvl2cnf,uvl2uvl}, built by `zig build` in parser/)
with no Python involved at all, not even at startup. See
uvllang.main.UVL(...).to_cnf() for the equivalent Python API, which
supports backend="lark"/"antlr" in addition to the zig default.

uvl2uvl reads a UVL model and writes a semantically equivalent UVL model
back out, keeping the input's feature hierarchy exactly as-is while
dropping any cross-tree constraint that's fully redundant given the
hierarchy and the other constraints (see `uvl2uvl --help`).
"""

import sys
import os
import argparse


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
        from uvllang.main import UVL

        model = UVL(from_file=uvl_file, backend="antlr" if use_antlr else "lark")
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
    parser.add_argument(
        "--propagate",
        action="store_true",
        help="Experimental: recover parent/child edges via unit propagation (BCP) in addition to "
        "literal clause matching, so edges eliminated by CNF subsumption/simplification can still "
        "be found. More expensive; off by default; meant for debugging/benchmarking for now.",
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
        from uvllang.main import UVL

        if args.verbose:
            print(f"Converting {input_file} to UVL format...")

        UVL.from_cnf(
            input_file,
            output_file,
            optimize=args.optimize,
            by_name=args.byname,
            verify=args.verify,
            infer_propagation=args.propagate,
        )

        print(f"Successfully converted to UVL format: {output_file}")

    except Exception as e:
        print(f"Error: {e}")
        if args.verbose:
            import traceback

            traceback.print_exc()
        sys.exit(1)

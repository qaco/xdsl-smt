#!/usr/bin/env python3

import argparse
import sys

from xdsl.ir import MLContext, Operation
from xdsl.parser import Parser

from ..dialects.smt_bitvector_dialect import SMTBitVectorDialect
from ..dialects.smt_dialect import CallOp, DefineFunOp, EqOp, AssertOp, SMTDialect
from ..dialects.smt_bitvector_dialect import SMTBitVectorDialect
from ..dialects.arith_dialect import Arith
from ..dialects.smt_utils_dialect import SMTUtilsDialect
from xdsl.dialects.builtin import Builtin, ModuleOp
from xdsl.dialects.func import Func

from ..passes.lower_pairs import LowerPairs
from ..passes.canonicalize_smt import CanonicalizeSMT
from ..passes.lower_to_smt import (
    LowerToSMT,
    arith_to_smt_patterns,
    comb_to_smt_patterns,
    transfer_to_smt_patterns,
    integer_type_lowerer,
    func_to_smt_patterns,
)

from ..traits.smt_printer import print_to_smtlib


def register_all_arguments(arg_parser: argparse.ArgumentParser):
    arg_parser.add_argument(
        "before_file", type=str, nargs="?", help="path to before input file"
    )

    arg_parser.add_argument(
        "after_file", type=str, nargs="?", help="path to after input file"
    )

    arg_parser.add_argument(
        "-opt",
        help="Optimize the SMTLib program by lowering "
        "pairs and applying constant folding.",
        action="store_true",
    )


def function_refinement(func: DefineFunOp, func_after: DefineFunOp) -> list[Operation]:
    """
    Create operations to check that one function refines another.
    An assert check is added to the end of the list of operations.
    """
    if len(func.body.blocks[0].args) != 0 or len(func_after.body.blocks[0].args) != 0:
        print("Function with arguments are not yet supported")
        exit(1)

    ops = list[Operation]()

    # Call both operations
    func_call = CallOp.get(func.results[0], [])
    func_call_after = CallOp.get(func_after.results[0], [])
    ops += [func_call, func_call_after]

    # Get the function return value
    ret_val = func_call.res
    ret_val_after = func_call_after.res

    refinement_op = EqOp(ret_val, ret_val_after)
    ops.append(refinement_op)

    ops.append(AssertOp(refinement_op.res))

    return ops


def main() -> None:
    ctx = MLContext()
    arg_parser = argparse.ArgumentParser()
    register_all_arguments(arg_parser)
    args = arg_parser.parse_args()

    # Register all dialects
    ctx.register_dialect(Arith)
    ctx.register_dialect(Builtin)
    ctx.register_dialect(Func)
    ctx.register_dialect(SMTDialect)
    ctx.register_dialect(SMTBitVectorDialect)
    ctx.register_dialect(SMTUtilsDialect)

    # Parse the files
    def parse_file(file: str | None) -> Operation:
        if file is None:
            f = sys.stdin
        else:
            f = open(file)

        parser = Parser(ctx, f.read())
        module = parser.parse_op()
        return module

    module = parse_file(args.before_file)
    module_after = parse_file(args.after_file)

    assert isinstance(module, ModuleOp)
    assert isinstance(module_after, ModuleOp)

    LowerToSMT.rewrite_patterns = [
        *arith_to_smt_patterns,
        *comb_to_smt_patterns,
        *transfer_to_smt_patterns,
        *func_to_smt_patterns,
    ]
    LowerToSMT.type_lowerers = [integer_type_lowerer]

    # Convert both module to SMTLib
    LowerToSMT().apply(ctx, module)
    LowerToSMT().apply(ctx, module_after)

    # Collect the function from both modules
    if (
        len(module.ops) != len(module_after.ops)
        or not isinstance(module.ops.first, DefineFunOp)
        or not isinstance(module_after.ops.first, DefineFunOp)
    ):
        print("Input is expected to have a single `func.func` operation.")
        exit(1)

    func = module.ops.first
    func_after = module_after.ops.first

    # Combine both modules into a new one
    new_module = ModuleOp([])
    block = new_module.body.blocks[0]
    func.detach()
    block.add_op(func)
    func_after.detach()
    block.add_op(func_after)

    # Add refinement operations
    block.add_ops(function_refinement(func, func_after))

    if args.opt:
        LowerPairs().apply(ctx, new_module)
        CanonicalizeSMT().apply(ctx, new_module)
    print_to_smtlib(new_module, sys.stdout)


if __name__ == "__main__":
    main()
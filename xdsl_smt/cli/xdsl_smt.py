#!/usr/bin/env python3

import argparse
from xdsl.xdsl_opt_main import xDSLOptMain

from xdsl.dialects.builtin import Builtin
from xdsl.dialects.func import Func
from xdsl.dialects.pdl import PDL
from xdsl.dialects.arith import Arith
from xdsl.dialects.comb import Comb

from xdsl_smt.passes.lower_to_smt.lower_to_smt import integer_poison_type_lowerer


from ..dialects.hoare_dialect import Hoare
from ..dialects.pdl_dataflow import PDLDataflowDialect
from ..dialects.smt_bitvector_dialect import SMTBitVectorDialect
from ..dialects.smt_dialect import SMTDialect
from ..dialects.smt_bitvector_dialect import SMTBitVectorDialect
from ..dialects.smt_utils_dialect import SMTUtilsDialect
from ..dialects.index_dialect import Index
from ..dialects.transfer import Transfer
from ..dialects.hw_dialect import HW
from ..dialects.llvm_dialect import LLVM

from ..passes.canonicalize_smt import CanonicalizeSMT
from ..passes.dead_code_elimination import DeadCodeElimination
from ..passes.lower_pairs import LowerPairs
from ..passes.lower_to_smt import (
    LowerToSMT,
    arith_to_smt_patterns,
    comb_to_smt_patterns,
    transfer_to_smt_patterns,
    integer_type_lowerer,
    func_to_smt_patterns,
    llvm_to_smt_patterns,
)
from ..passes.pdl_to_smt import PDLToSMT

from ..traits.smt_printer import print_to_smtlib


class OptMain(xDSLOptMain):
    def register_all_dialects(self):
        self.ctx.register_dialect(Arith)
        self.ctx.register_dialect(Builtin)
        self.ctx.register_dialect(Func)
        self.ctx.register_dialect(Index)
        self.ctx.register_dialect(SMTDialect)
        self.ctx.register_dialect(SMTBitVectorDialect)
        self.ctx.register_dialect(SMTUtilsDialect)
        self.ctx.register_dialect(Transfer)
        self.ctx.register_dialect(Hoare)
        self.ctx.register_dialect(PDL)
        self.ctx.register_dialect(PDLDataflowDialect)
        self.ctx.register_dialect(Comb)
        self.ctx.register_dialect(HW)
        self.ctx.register_dialect(LLVM)

    def register_all_passes(self):
        super().register_all_passes()
        self.register_pass(LowerToSMT)
        self.register_pass(DeadCodeElimination)
        self.register_pass(CanonicalizeSMT)
        self.register_pass(LowerPairs)
        self.register_pass(PDLToSMT)

    def register_all_arguments(self, arg_parser: argparse.ArgumentParser):
        arg_parser.add_argument(
            "--circt",
            default=False,
            action="store_true",
            help="Handle only func and comb dialects",
        )
        super().register_all_arguments(arg_parser)

    def register_all_targets(self):
        super().register_all_targets()
        self.available_targets["smt"] = print_to_smtlib


def main():
    xdsl_main = OptMain()
    if xdsl_main.args.circt:
        LowerToSMT.rewrite_patterns = [
            *comb_to_smt_patterns,
            *func_to_smt_patterns,
            *llvm_to_smt_patterns,
        ]
        LowerToSMT.type_lowerers = [integer_type_lowerer]
    else:
        LowerToSMT.rewrite_patterns = [
            *arith_to_smt_patterns,
            *transfer_to_smt_patterns,
            *func_to_smt_patterns,
            *llvm_to_smt_patterns,
        ]
        LowerToSMT.type_lowerers = [integer_poison_type_lowerer]

    xdsl_main.run()


if __name__ == "__main__":
    main()

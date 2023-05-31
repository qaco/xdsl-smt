from xdsl.pattern_rewriter import (
    RewritePattern,
    op_type_rewrite_pattern,
    PatternRewriter,
    PatternRewriteWalker,
    GreedyRewritePatternApplier,
)
from xdsl.passes import ModulePass
from xdsl.ir import MLContext, Operation
from xdsl.dialects.builtin import ModuleOp

from .arith_to_smt import FuncToSMTPattern, ReturnPattern, convert_type
from dialects import comb
import dialects.smt_bitvector_dialect as bv_dialect
import dialects.smt_dialect as core_dialect


def variadic_op_pattern(
    comb_op_type: type[comb.VariadicCombOp],
    smt_op_type: type[Operation],
    empty_value: int,
) -> RewritePattern:
    class VariadicOpPattern(RewritePattern):
        def match_and_rewrite(self, op: Operation, rewriter: PatternRewriter):
            if not isinstance(op, comb_op_type):
                return
            if len(op.operands) == 0:
                rewriter.replace_matched_op(bv_dialect.ConstantOp(empty_value, 1))
                return

            current_val = op.operands[0]

            for operand in op.operands[1:]:
                new_op = smt_op_type(
                    operands=[current_val, operand],
                    result_types=[convert_type(op.result.typ)],
                )
                current_val = new_op.results[0]
                rewriter.insert_op_before_matched_op(new_op)

            rewriter.replace_matched_op([], [current_val])

    return VariadicOpPattern()


def trivial_binop_pattern(
    comb_op_type: type[comb.BinCombOp], smt_op_type: type[Operation]
) -> RewritePattern:
    class TrivialBinOpPattern(RewritePattern):
        def match_and_rewrite(self, op: Operation, rewriter: PatternRewriter):
            if not isinstance(op, comb_op_type):
                return
            new_op = smt_op_type(
                operands=op.operands,
                result_types=[convert_type(op.result.typ)],
            )
            rewriter.replace_matched_op([new_op])
            return super().match_and_rewrite(op, rewriter)

    return TrivialBinOpPattern()


class ICmpPattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: comb.ICmpOp, rewriter: PatternRewriter) -> None:
        raise NotImplementedError()


class ParityPattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: comb.ParityOp, rewriter: PatternRewriter) -> None:
        raise NotImplementedError()


class ExtractPattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: comb.ExtractOp, rewriter: PatternRewriter) -> None:
        raise NotImplementedError()


class ConcatPattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: comb.ConcatOp, rewriter: PatternRewriter) -> None:
        assert len(op.operands) > 0

        current_val = op.operands[0]

        for operand in op.operands[1:]:
            new_op = bv_dialect.ConcatOp(current_val, operand)
            current_val = new_op.results[0]
            rewriter.insert_op_before_matched_op(new_op)

        rewriter.replace_matched_op([], [current_val])


class ReplicatePattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(
        self, op: comb.ReplicateOp, rewriter: PatternRewriter
    ) -> None:
        raise NotImplementedError()


class MuxPattern(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: comb.MuxOp, rewriter: PatternRewriter) -> None:
        rewriter.replace_matched_op(
            [core_dialect.IteOp(op.cond, op.true_value, op.false_value)]
        )


comb_to_smt_patterns: list[RewritePattern] = [
    variadic_op_pattern(comb.AddOp, bv_dialect.AddOp, 0),
    variadic_op_pattern(comb.MulOp, bv_dialect.MulOp, 1),
    trivial_binop_pattern(comb.DivUOp, bv_dialect.UDivOp),
    trivial_binop_pattern(comb.DivSOp, bv_dialect.SDivOp),
    trivial_binop_pattern(comb.ModUOp, bv_dialect.URemOp),
    trivial_binop_pattern(comb.ModSOp, bv_dialect.SRemOp),
    trivial_binop_pattern(comb.ShlOp, bv_dialect.ShlOp),
    trivial_binop_pattern(comb.ShrUOp, bv_dialect.LShrOp),
    trivial_binop_pattern(comb.ShrSOp, bv_dialect.AShrOp),
    trivial_binop_pattern(comb.SubOp, bv_dialect.SubOp),
    variadic_op_pattern(comb.OrOp, bv_dialect.OrOp, 0),
    variadic_op_pattern(comb.AndOp, bv_dialect.AndOp, 1),
    variadic_op_pattern(comb.XorOp, bv_dialect.XorOp, 0),
    ICmpPattern(),
    ParityPattern(),
    ExtractPattern(),
    ConcatPattern(),
    ReplicatePattern(),
    MuxPattern(),
]


class CombToSMT(ModulePass):
    name = "comb-to-smt"

    def apply(self, ctx: MLContext, op: ModuleOp):
        walker = PatternRewriteWalker(
            GreedyRewritePatternApplier(
                [*comb_to_smt_patterns, FuncToSMTPattern(), ReturnPattern()]
            )
        )
        walker.rewrite_module(op)
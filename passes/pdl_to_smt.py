from dataclasses import dataclass, field
from xdsl.dialects.builtin import ModuleOp
from xdsl.dialects.pdl import (
    OperandOp,
    OperationOp,
    PatternOp,
    ReplaceOp,
    ResultOp,
    RewriteOp,
    TypeOp,
    AttributeOp,
)
from xdsl.irdl import IRDLOperation

from dialects import pdl_dataflow as pdl_dataflow
from dialects import smt_bitvector_dialect as smt_bv
from dialects import transfer

from xdsl.ir import Attribute, ErasedSSAValue, MLContext, Operation, SSAValue

from xdsl.pattern_rewriter import (
    GreedyRewritePatternApplier,
    PatternRewriteWalker,
    PatternRewriter,
    RewritePattern,
    op_type_rewrite_pattern,
)
from xdsl.passes import ModulePass
from dialects.smt_dialect import (
    AndOp,
    AssertOp,
    CheckSatOp,
    DeclareConstOp,
    DistinctOp,
    EqOp,
    NotOp,
)

from passes.arith_to_smt import ArithToSMT, convert_type, arith_to_smt_patterns
from passes.comb_to_smt import CombToSMT, comb_to_smt_patterns


@dataclass
class PDLToSMTRewriteContext:
    pdl_op_to_op: dict[SSAValue, Operation] = field(default_factory=dict)
    preconditions: list[SSAValue] = field(default_factory=list)


def _get_type_of_erased_type_value(value: SSAValue) -> Attribute:
    assert isinstance(value, ErasedSSAValue), "Error in rewriting logic"
    assert isinstance(
        (type_op := value.old_value.owner), TypeOp
    ), "Error in rewriting logic"
    type = type_op.constantType
    if type is None:
        raise Exception("Cannot handle non-constant types")
    return type


def _get_attr_of_erased_attr_value(value: SSAValue) -> Attribute:
    assert isinstance(value, ErasedSSAValue), "Error in rewriting logic"
    assert isinstance(
        (attr_op := value.old_value.owner), AttributeOp
    ), "Error in rewriting logic"
    attr = attr_op.value
    if attr is None:
        raise Exception("Cannot handle non-constant attributes")
    return attr


class PatternRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: PatternOp, rewriter: PatternRewriter):
        rewriter.inline_block_before_matched_op(op.body.blocks[0])
        rewriter.insert_op_before_matched_op(CheckSatOp())
        rewriter.erase_matched_op()


class RewriteRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: RewriteOp, rewriter: PatternRewriter):
        if op.body is not None:
            rewriter.inline_block_before_matched_op(op.body.blocks[0])
        rewriter.erase_matched_op()


class DataflowRewriteRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: pdl_dataflow.RewriteOp, rewriter: PatternRewriter):
        rewriter.inline_block_before_matched_op(op.body.blocks[0])
        rewriter.erase_matched_op()


class TypeRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: TypeOp, rewriter: PatternRewriter):
        rewriter.erase_matched_op(safe_erase=False)


class AttributeRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: AttributeOp, rewriter: PatternRewriter):
        rewriter.erase_matched_op(safe_erase=False)


class OperandRewrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: OperandOp, rewriter: PatternRewriter):
        if op.value_type is None:
            raise Exception("Cannot handle non-typed operands")
        type = _get_type_of_erased_type_value(op.value_type)
        smt_type = convert_type(type)
        rewriter.replace_matched_op(DeclareConstOp(smt_type))


@dataclass
class OperationRewrite(RewritePattern):
    ctx: MLContext
    rewrite_context: PDLToSMTRewriteContext

    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: OperationOp, rewriter: PatternRewriter):
        # Get the corresponding op definition from the context
        if op.opName is None:
            raise Exception("Cannot handle non-constant op names")
        op_def = self.ctx.get_op(op.opName.data)

        # Create the with the given operands and types
        result_types = [_get_type_of_erased_type_value(type) for type in op.type_values]
        attributes = {
            name.data: _get_attr_of_erased_attr_value(attr)
            for attr, name in zip(op.attribute_values, op.attributeValueNames)
        }
        synthesized_op = op_def.create(
            operands=op.operand_values, result_types=result_types, attributes=attributes
        )

        # Cursed hack: we create a new module with that operation, and
        # we rewrite it with the arith_to_smt and comb_to_smt pass.
        rewrite_module = ModuleOp([synthesized_op])
        ArithToSMT().apply(self.ctx, rewrite_module)
        CombToSMT().apply(self.ctx, rewrite_module)
        last_op = rewrite_module.body.block.last_op
        assert last_op is not None

        # Set the operation carrying the results in the context
        # FIXME: this does not work if the last operation does not return all results
        self.rewrite_context.pdl_op_to_op[op.op] = last_op
        rewriter.inline_block_before_matched_op(rewrite_module.body.blocks[0])

        rewriter.erase_matched_op(safe_erase=False)


@dataclass
class ReplaceRewrite(RewritePattern):
    rewrite_context: PDLToSMTRewriteContext

    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: ReplaceOp, rewriter: PatternRewriter):
        assert isinstance(op.op_value, ErasedSSAValue)
        replaced_op = self.rewrite_context.pdl_op_to_op[op.op_value.old_value]
        if len(replaced_op.results) != 1:
            raise Exception("Cannot handle operations with multiple results")

        replacing_value: SSAValue
        # Replacing by values case
        if len(op.repl_values) != 0:
            assert len(op.repl_values) == 1
            replacing_value = op.repl_values[0]
        # Replacing by operations case
        else:
            assert isinstance(op.repl_operation, ErasedSSAValue)
            replacing_op = self.rewrite_context.pdl_op_to_op[
                op.repl_operation.old_value
            ]
            if len(replacing_op.results) != 1:
                raise Exception("Cannot handle operations with multiple results")
            replacing_value = replacing_op.results[0]

        distinct_op = DistinctOp(replacing_value, replaced_op.results[0])

        if len(self.rewrite_context.preconditions) == 0:
            assert_op = AssertOp(distinct_op.res)
            rewriter.replace_matched_op([distinct_op, assert_op])
            return

        and_preconditions = self.rewrite_context.preconditions[0]
        for precondition in self.rewrite_context.preconditions[1:]:
            and_preconditions_op = AndOp(and_preconditions, precondition)
            rewriter.insert_op_before_matched_op(and_preconditions_op)
            and_preconditions = and_preconditions_op.res

        replace_correct = AndOp(distinct_op.res, and_preconditions)
        assert_op = AssertOp(replace_correct.res)
        rewriter.replace_matched_op([distinct_op, replace_correct, assert_op])


@dataclass
class ResultRewrite(RewritePattern):
    rewrite_context: PDLToSMTRewriteContext

    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: ResultOp, rewriter: PatternRewriter):
        assert isinstance(op.parent_, ErasedSSAValue)
        result = self.rewrite_context.pdl_op_to_op[op.parent_.old_value].results[
            op.index.value.data
        ]
        rewriter.replace_matched_op([], new_results=[result])


def kb_analysis_correct(
    value: SSAValue, zeros: SSAValue, ones: SSAValue
) -> tuple[SSAValue, list[Operation]]:
    assert isinstance(value.type, smt_bv.BitVectorType)
    and_op_zeros = smt_bv.AndOp(value, zeros)
    zero = smt_bv.ConstantOp(0, value.type.width.data)
    zeros_correct = EqOp(and_op_zeros.res, zero.res)
    and_op_ones = smt_bv.AndOp(value, ones)
    ones_correct = EqOp(and_op_ones.res, ones)
    all_correct = AndOp(zeros_correct.res, ones_correct.res)
    return all_correct.res, [
        and_op_zeros,
        zero,
        zeros_correct,
        and_op_ones,
        ones_correct,
        all_correct,
    ]


@dataclass
class GetOpRewrite(RewritePattern):
    rewrite_context: PDLToSMTRewriteContext

    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: pdl_dataflow.GetOp, rewriter: PatternRewriter):
        assert isinstance(op.value.type, smt_bv.BitVectorType)
        bv_type = op.value.type
        zeros_op = DeclareConstOp(bv_type)
        ones_op = DeclareConstOp(bv_type)

        value = op.value
        zeros = zeros_op.res
        ones = ones_op.res

        all_correct, correct_ops = kb_analysis_correct(value, zeros, ones)
        self.rewrite_context.preconditions.append(all_correct)

        rewriter.replace_matched_op(
            [
                zeros_op,
                ones_op,
                *correct_ops,
            ],
            new_results=[zeros, ones],
        )
        name = op.value.name_hint if op.value.name_hint else "value"
        zeros.name_hint = name + "_zeros"
        ones.name_hint = name + "_ones"


@dataclass
class AttachOpRewrite(RewritePattern):
    rewrite_context: PDLToSMTRewriteContext

    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: pdl_dataflow.AttachOp, rewriter: PatternRewriter):
        assert len(op.domains) == 2
        zeros, ones = op.domains

        analysis_correct, analysis_correct_ops = kb_analysis_correct(
            op.value, zeros, ones
        )
        rewriter.insert_op_before_matched_op(analysis_correct_ops)
        analysis_incorrect_op = NotOp.get(analysis_correct)
        rewriter.insert_op_before_matched_op(analysis_incorrect_op)
        analysis_incorrect = analysis_incorrect_op.res

        if len(self.rewrite_context.preconditions) == 0:
            rewriter.replace_matched_op(AssertOp(analysis_incorrect))
            return

        and_preconditions = self.rewrite_context.preconditions[0]
        for precondition in self.rewrite_context.preconditions[1:]:
            and_preconditions_op = AndOp(and_preconditions, precondition)
            rewriter.insert_op_before_matched_op(and_preconditions_op)
            and_preconditions = and_preconditions_op.res

        implies = AndOp(and_preconditions, analysis_incorrect)
        rewriter.insert_op_before_matched_op(implies)
        rewriter.replace_matched_op(AssertOp(implies.res))


def trivial_pattern(
    match_type: type[IRDLOperation], rewrite_type: type[IRDLOperation]
) -> RewritePattern:
    class TrivialBinOpPattern(RewritePattern):
        def match_and_rewrite(self, op: Operation, rewriter: PatternRewriter):
            if not isinstance(op, match_type):
                return
            # TODO: How to handle multiple results, or results with different types?
            new_op = rewrite_type.create(
                operands=op.operands,
                result_types=[op.operands[0].type],
            )
            rewriter.replace_matched_op([new_op])

    return TrivialBinOpPattern()


class PDLToSMT(ModulePass):
    name = "pdl-to-smt"

    def apply(self, ctx: MLContext, op: ModuleOp) -> None:
        rewrite_context = PDLToSMTRewriteContext({})
        walker = PatternRewriteWalker(
            GreedyRewritePatternApplier(
                [
                    PatternRewrite(),
                    RewriteRewrite(),
                    DataflowRewriteRewrite(),
                    TypeRewrite(),
                    AttributeRewrite(),
                    OperandRewrite(),
                    GetOpRewrite(rewrite_context),
                    OperationRewrite(ctx, rewrite_context),
                    ReplaceRewrite(rewrite_context),
                    ResultRewrite(rewrite_context),
                    AttachOpRewrite(rewrite_context),
                    trivial_pattern(transfer.AndOp, smt_bv.AndOp),
                    trivial_pattern(transfer.OrOp, smt_bv.OrOp),
                    *arith_to_smt_patterns,
                    *comb_to_smt_patterns,
                ]
            )
        )
        walker.rewrite_module(op)

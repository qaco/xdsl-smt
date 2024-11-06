from abc import abstractmethod, ABC
from xdsl_smt.semantics.semantics import OperationSemantics, TypeSemantics
from typing import Mapping, Sequence, cast
from xdsl.ir import SSAValue, Attribute, Region, Block
from xdsl.pattern_rewriter import PatternRewriter
from xdsl.utils.hints import isa
from xdsl.dialects.builtin import IntegerType, AnyIntegerAttr, IntegerAttr
from xdsl_smt.dialects.smt_dialect import BoolType
from xdsl_smt.dialects import smt_int_dialect as smt_int
from xdsl_smt.dialects import smt_dialect as smt
from xdsl_smt.dialects import smt_utils_dialect as smt_utils
from xdsl_smt.dialects.effects import ub_effect as smt_ub
from xdsl_smt.semantics.semantics import RefinementSemantics
from xdsl_smt.dialects.effects import ub_effect
from xdsl.dialects.builtin import Signedness


class IntIntegerTypeRefinementSemantics(RefinementSemantics):
    def get_semantics(
        self,
        val_before: SSAValue,
        val_after: SSAValue,
        state_before: SSAValue,
        state_after: SSAValue,
        rewriter: PatternRewriter,
    ) -> SSAValue:
        """Compute the refinement from a value with poison semantics to a value with poison semantics."""
        before_inner_loop = smt_utils.FirstOp(val_before)
        after_inner_loop = smt_utils.FirstOp(val_after)

        before_poison = smt_utils.SecondOp(before_inner_loop.res)
        after_poison = smt_utils.SecondOp(after_inner_loop.res)

        before_val = smt_utils.FirstOp(before_inner_loop.res)
        after_val = smt_utils.FirstOp(after_inner_loop.res)

        rewriter.insert_op_before_matched_op(
            [
                before_inner_loop,
                after_inner_loop,
                before_poison,
                after_poison,
                before_val,
                after_val,
            ]
        )

        not_before_poison = smt.NotOp(before_poison.res)
        not_after_poison = smt.NotOp(after_poison.res)

        width_type = smt_int.SMTIntType()
        body = Region([Block(arg_types=[width_type])])

        var = body.first_block.args[0]
        mod_before = smt_int.ModOp(before_val.res, var)
        mod_after = smt_int.ModOp(after_val.res, var)
        eq_op = smt.EqOp(mod_before.res, mod_after.res)
        yield_op = smt.YieldOp(eq_op.res)
        body.first_block.add_ops([mod_before, mod_after, eq_op, yield_op])

        forall_op = smt.ForallOp.create(result_types=[BoolType()], regions=[body])
        not_poison_eq = smt.AndOp(forall_op.res, not_after_poison.res)
        refinement_integer = smt.ImpliesOp(not_before_poison.res, not_poison_eq.res)
        rewriter.insert_op_before_matched_op(
            [
                not_before_poison,
                not_after_poison,
                forall_op,
                not_poison_eq,
                refinement_integer,
            ]
        )

        # With UB, our refinement is: ub_before \/ (not ub_after /\ integer_refinement)
        ub_before_bool = ub_effect.ToBoolOp(state_before)
        ub_after_bool = ub_effect.ToBoolOp(state_after)
        not_ub_after = smt.NotOp(ub_after_bool.res)
        not_ub_before_case = smt.AndOp(not_ub_after.res, refinement_integer.res)
        refinement = smt.OrOp(ub_before_bool.res, not_ub_before_case.res)
        rewriter.insert_op_before_matched_op(
            [
                ub_before_bool,
                ub_after_bool,
                not_ub_after,
                not_ub_before_case,
                refinement,
            ]
        )
        return refinement.res


class IntIntegerTypeSemantics(TypeSemantics):
    def get_semantics(self, type: Attribute) -> Attribute:
        assert isinstance(type, IntegerType)
        inner_pair_type = smt_utils.PairType(smt_int.SMTIntType(), smt.BoolType())
        outer_pair_type = smt_utils.PairType(inner_pair_type, smt_int.SMTIntType())
        return outer_pair_type


class IntConstantSemantics(OperationSemantics):
    def get_semantics(
        self,
        operands: Sequence[SSAValue],
        results: Sequence[Attribute],
        attributes: Mapping[str, Attribute | SSAValue],
        effect_state: SSAValue | None,
        rewriter: PatternRewriter,
    ) -> tuple[Sequence[SSAValue], SSAValue | None]:
        value_value = attributes["value"]
        assert isa(value_value, AnyIntegerAttr)
        assert len(results) == 1
        assert isa(results[0], IntegerType)
        literal = smt_int.ConstantOp(value_value.value.data)
        rewriter.insert_op_before_matched_op([literal])
        int_max = smt_int.ConstantOp(2 ** results[0].width.data)
        modulo = smt_int.ModOp(literal.res, int_max.res)
        no_poison = smt.ConstantBoolOp.from_bool(False)
        inner_pair = smt_utils.PairOp(modulo.res, no_poison.res)
        outer_pair = smt_utils.PairOp(inner_pair.res, int_max.res)
        rewriter.insert_op_before_matched_op(
            [int_max, modulo, no_poison, inner_pair, outer_pair]
        )
        return ((outer_pair.res,), effect_state)


class GenericIntBinarySemantics(OperationSemantics, ABC):
    """
    Generic semantics of binary operations on parametric integers.
    """

    def get_semantics(
        self,
        operands: Sequence[SSAValue],
        results: Sequence[Attribute],
        attributes: Mapping[str, Attribute | SSAValue],
        effect_state: SSAValue | None,
        rewriter: PatternRewriter,
    ) -> tuple[Sequence[SSAValue], SSAValue | None]:
        lhs = operands[0]
        rhs = operands[1]
        # Unpack
        lhs_get_inner_pair = smt_utils.FirstOp(lhs)
        rhs_get_inner_pair = smt_utils.FirstOp(rhs)
        lhs_get_int_max = smt_utils.SecondOp(lhs)
        rhs_get_int_max = smt_utils.SecondOp(rhs)
        # Compute the payload
        lhs_get_payload = smt_utils.FirstOp(lhs_get_inner_pair.res)
        rhs_get_payload = smt_utils.FirstOp(rhs_get_inner_pair.res)
        rewriter.insert_op_before_matched_op(
            [
                lhs_get_inner_pair,
                rhs_get_inner_pair,
                lhs_get_int_max,
                rhs_get_int_max,
                lhs_get_payload,
                rhs_get_payload,
            ]
        )
        assert effect_state
        effect_state = self.get_ub(
            lhs_get_payload.res, rhs_get_payload.res, effect_state, rewriter
        )
        payload = self.get_payload_semantics(
            lhs_get_payload.res,
            rhs_get_payload.res,
            lhs_get_int_max.res,
            attributes,
            rewriter,
        )
        # Compute the poison
        lhs_get_poison = smt_utils.SecondOp(lhs_get_inner_pair.res)
        rhs_get_poison = smt_utils.SecondOp(rhs_get_inner_pair.res)
        rewriter.insert_op_before_matched_op([lhs_get_poison, rhs_get_poison])
        poison = self.get_poison(
            lhs_get_poison.res,
            rhs_get_poison.res,
            lhs_get_payload.res,
            rhs_get_payload.res,
            payload,
            rewriter,
        )
        # Pack
        inner_pair = smt_utils.PairOp(payload, poison)
        outer_pair = smt_utils.PairOp(inner_pair.res, lhs_get_int_max.res)
        rewriter.insert_op_before_matched_op([inner_pair, outer_pair])
        return ((outer_pair.res,), effect_state)

    def get_poison(
        self,
        poison0: SSAValue,
        poison1: SSAValue,
        lhs: SSAValue,
        rhs: SSAValue,
        res: SSAValue,
        rewriter: PatternRewriter,
    ) -> SSAValue:
        or_poison = smt.OrOp(poison0, poison1)
        rewriter.insert_op_before_matched_op([or_poison])
        return or_poison.res

    @abstractmethod
    def get_ub(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        effect_state: SSAValue,
        rewriter: PatternRewriter,
    ) -> SSAValue:
        ...

    @abstractmethod
    def get_payload_semantics(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        int_max: SSAValue,
        attributes: Mapping[str, Attribute | SSAValue],
        rewriter: PatternRewriter,
    ) -> SSAValue:
        ...


class IntDivBasedSemantics(GenericIntBinarySemantics):
    @abstractmethod
    def _get_payload_semantics(
        self, lhs: SSAValue, rhs: SSAValue, rewriter: PatternRewriter
    ) -> SSAValue:
        ...

    def get_ub(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        effect_state: SSAValue,
        rewriter: PatternRewriter,
    ) -> SSAValue:
        zero_op = smt_int.ConstantOp(0)
        rewriter.insert_op_before_matched_op([zero_op])
        is_div_by_zero = smt.EqOp(rhs, zero_op.res)
        trigger_ub = smt_ub.TriggerOp(effect_state)
        new_state = smt.IteOp(is_div_by_zero.res, trigger_ub.res, effect_state)
        rewriter.insert_op_before_matched_op([is_div_by_zero, trigger_ub, new_state])
        return effect_state

    def get_payload_semantics(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        int_max: SSAValue,
        attributes: Mapping[str, Attribute | SSAValue],
        rewriter: PatternRewriter,
    ) -> SSAValue:
        return self._get_payload_semantics(lhs, rhs, rewriter)


class IntBinaryEFSemantics(GenericIntBinarySemantics):
    """
    Semantics of binary operations on parametric integers which can not have an effect
    (Effect-Free).
    """

    def get_ub(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        effect_state: SSAValue,
        rewriter: PatternRewriter,
    ) -> SSAValue:
        return effect_state

    @abstractmethod
    def _get_payload_semantics(
        self, lhs: SSAValue, rhs: SSAValue, rewriter: PatternRewriter
    ) -> SSAValue:
        ...

    def get_payload_semantics(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        int_max: SSAValue,
        attributes: Mapping[str, Attribute | SSAValue],
        rewriter: PatternRewriter,
    ) -> SSAValue:
        payload = self._get_payload_semantics(lhs, rhs, rewriter)
        modulo = smt_int.ModOp(payload, int_max)
        rewriter.insert_op_before_matched_op([modulo])
        return modulo.res


class IntCmpiSemantics(GenericIntBinarySemantics):
    def get_ub(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        effect_state: SSAValue,
        rewriter: PatternRewriter,
    ):
        return effect_state

    def get_payload_semantics(
        self,
        lhs: SSAValue,
        rhs: SSAValue,
        int_max: SSAValue,
        attributes: Mapping[str, Attribute | SSAValue],
        rewriter: PatternRewriter,
    ) -> SSAValue:
        integer_attr = cast(IntegerAttr[IntegerType], attributes["predicate"])
        match integer_attr.value.data:
            case 0:
                payload_op = smt.EqOp(lhs, rhs)
            case 1:
                payload_op = smt.DistinctOp(lhs, rhs)
            case 2:
                raise NotImplementedError()
            case 3:
                raise NotImplementedError()
            case 4:
                raise NotImplementedError()
            case 5:
                raise NotImplementedError()
            case 6:
                payload_op = smt_int.LtOp(lhs, rhs)
            case 7:
                payload_op = smt_int.LeOp(lhs, rhs)
            case 8:
                payload_op = smt_int.GtOp(lhs, rhs)
            case 9:
                payload_op = smt_int.GeOp(lhs, rhs)
            case _:
                assert False

        rewriter.insert_op_before_matched_op([payload_op])
        payload = payload_op.res

        return payload


def get_binary_ef_semantics(new_operation: type[smt_int.BinaryIntOp]):
    class OpSemantics(IntBinaryEFSemantics):
        def _get_payload_semantics(
            self,
            lhs: SSAValue,
            rhs: SSAValue,
            rewriter: PatternRewriter,
        ) -> SSAValue:
            payload_op = new_operation(lhs, rhs)
            assert not isinstance(payload_op, smt_int.DivOp)
            assert not isinstance(payload_op, smt_int.ModOp)
            rewriter.insert_op_before_matched_op([payload_op])
            return payload_op.res

    return OpSemantics


def get_div_semantics(new_operation: type[smt_int.BinaryIntOp]):
    class OpSemantics(IntDivBasedSemantics):
        def _get_payload_semantics(
            self,
            lhs: SSAValue,
            rhs: SSAValue,
            rewriter: PatternRewriter,
        ) -> SSAValue:
            payload_op = new_operation(lhs, rhs)
            assert isinstance(payload_op, smt_int.DivOp) or isinstance(
                payload_op, smt_int.ModOp
            )
            rewriter.insert_op_before_matched_op([payload_op])
            return payload_op.res

    return OpSemantics

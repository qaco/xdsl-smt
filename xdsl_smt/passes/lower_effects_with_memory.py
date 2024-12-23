from dataclasses import dataclass

from xdsl.ir import Attribute, ParametrizedAttribute, Operation, SSAValue
from xdsl.utils.isattr import isattr
from xdsl.passes import ModulePass
from xdsl.context import MLContext
from xdsl.pattern_rewriter import (
    PatternRewriteWalker,
    GreedyRewritePatternApplier,
    RewritePattern,
    PatternRewriter,
    op_type_rewrite_pattern,
)

from xdsl.dialects.builtin import ModuleOp, AnyArrayAttr
from xdsl_smt.dialects.effects import memory_effect as mem_effect, ub_effect
from xdsl_smt.dialects.smt_bitvector_dialect import BitVectorType
from xdsl_smt.dialects.smt_dialect import BoolType
from xdsl_smt.dialects.effects import effect, memory_effect as mem_effect
from xdsl_smt.dialects import (
    memory_dialect as mem,
    smt_utils_dialect as smt_utils,
    smt_dialect as smt,
    smt_bitvector_dialect as smt_bv,
)

new_state_type = smt_utils.PairType(mem.MemoryType(), BoolType())
new_pointer_type = smt_utils.PairType(mem.BlockIDType(), BitVectorType(64))


def get_memory_and_ub_from_state(
    state: SSAValue, rewriter: PatternRewriter
) -> tuple[SSAValue, SSAValue]:
    """Get the ub flag and memory from a state value."""
    memory = smt_utils.FirstOp(state, new_state_type)
    ub = smt_utils.SecondOp(state, new_state_type)
    rewriter.insert_op_before_matched_op([memory, ub])
    memory.res.name_hint = "memory"
    ub.res.name_hint = "ub_marker"
    return memory.res, ub.res


def create_state(memory: SSAValue, ub: SSAValue, rewriter: PatternRewriter) -> SSAValue:
    """Create a state value from the ub flag and memory state."""
    state = smt_utils.PairOp(memory, ub)
    rewriter.insert_op_before_matched_op([state])
    state.res.name_hint = "state"
    return state.res


def get_block_id_and_offset_from_pointer(
    pointer: SSAValue, rewriter: PatternRewriter
) -> tuple[SSAValue, SSAValue]:
    """Get the block ID and offset from a pointer value."""
    block_id = smt_utils.FirstOp(pointer, new_pointer_type)
    offset = smt_utils.SecondOp(pointer, new_pointer_type)
    rewriter.insert_op_before_matched_op([block_id, offset])
    block_id.res.name_hint = "block_id"
    offset.res.name_hint = "ptr_offset"
    return block_id.res, offset.res


def create_pointer(
    block_id: SSAValue, offset: SSAValue, rewriter: PatternRewriter
) -> SSAValue:
    """Create a pointer value from the block ID and offset."""
    pointer = smt_utils.PairOp(block_id, offset)
    rewriter.insert_op_before_matched_op([pointer])
    pointer.res.name_hint = "ptr"
    return pointer.res


def check_bounds(
    offset: SSAValue,
    block: SSAValue,
    rewriter: PatternRewriter,
) -> SSAValue:
    """Check if a pointer access is within the bounds of the memory."""

    # Get the block size
    block_size_op = mem.GetBlockSizeOp(block)
    rewriter.insert_op_before_matched_op([block_size_op])
    block_size = block_size_op.res
    block_size.name_hint = "block_size"

    # Check that the offset of the end bit is within the bounds
    offset_end_op = smt_bv.AddOp(offset, block_size_op.res)
    offset_in_bounds_op = smt_bv.UleOp(offset_end_op.res, block_size)
    rewriter.insert_op_before_matched_op([offset_end_op, offset_in_bounds_op])
    offset_in_bounds_op.res.name_hint = "offset_in_bounds"

    return offset_in_bounds_op.res


def recursively_convert_attr(attr: Attribute) -> Attribute:
    """
    Recursively convert an attribute to replace all references to the effect state
    into a pair between the ub flag and the memory.
    """
    if isinstance(attr, effect.StateType):
        return smt_utils.PairType(mem.MemoryType(), BoolType())
    if isinstance(attr, mem_effect.PointerType):
        return smt_utils.PairType(mem.BlockIDType(), BitVectorType(64))
    if isinstance(attr, ParametrizedAttribute):
        return type(attr).new(
            [recursively_convert_attr(param) for param in attr.parameters]
        )
    if isattr(attr, AnyArrayAttr):
        return AnyArrayAttr((recursively_convert_attr(value) for value in attr.data))
    return attr


class LowerTriggerOp(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: ub_effect.TriggerOp, rewriter: PatternRewriter):
        memory, _ = get_memory_and_ub_from_state(op.state, rewriter)
        new_ub = smt.ConstantBoolOp(True)
        rewriter.insert_op_before_matched_op([new_ub])
        new_state = create_state(memory, new_ub.res, rewriter)
        rewriter.replace_matched_op([], [new_state])


class LowerToBoolOp(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: ub_effect.ToBoolOp, rewriter: PatternRewriter):
        _, ub = get_memory_and_ub_from_state(op.state, rewriter)
        rewriter.replace_matched_op([], new_results=[ub])


class LowerGenericOp(RewritePattern):
    """
    Recursively lower all result types, attributes, and properties that reference
    effect states.
    """

    def match_and_rewrite(self, op: Operation, rewriter: PatternRewriter):
        for result in op.results:
            if (new_type := recursively_convert_attr(result.type)) != result.type:
                rewriter.modify_value_type(result, new_type)

        for region in op.regions:
            for block in region.blocks:
                for arg in block.args:
                    if (new_type := recursively_convert_attr(arg.type)) != arg.type:
                        rewriter.modify_value_type(arg, new_type)

        has_done_action = False
        for name, attr in op.attributes.items():
            if (new_attr := recursively_convert_attr(attr)) != attr:
                op.attributes[name] = new_attr
                has_done_action = True
        for name, attr in op.properties.items():
            if (new_attr := recursively_convert_attr(attr)) != attr:
                op.properties[name] = new_attr
                has_done_action = True
        if has_done_action:
            rewriter.handle_operation_modification(op)


class LowerAlloc(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: mem_effect.AllocOp, rewriter: PatternRewriter):
        memory, ub = get_memory_and_ub_from_state(op.state, rewriter)

        # Get a fresh block ID
        id_op = mem.GetFreshBlockIDOp(memory)
        rewriter.insert_op_before_matched_op([id_op])
        memory = id_op.new_memory

        # Get the given block and set it as live with the given size
        get_block_op = mem.GetBlockOp(memory, id_op.res)
        block = get_block_op.res
        true_op = smt.ConstantBoolOp(True)
        set_live_op = mem.SetBlockLiveMarkerOp(block, true_op.res)
        block = set_live_op.res
        set_block_size = mem.SetBlockSizeOp(set_live_op.res, op.size)
        block = set_block_size.res
        rewriter.insert_op_before_matched_op(
            [get_block_op, true_op, set_live_op, set_block_size]
        )

        # Put it back to the memory
        new_memory_op = mem.SetBlockOp(block, memory, id_op.res)
        rewriter.insert_op_before_matched_op([new_memory_op])

        # Get a pointer to the block
        zero_index_op = smt_bv.ConstantOp(0, 64)
        rewriter.insert_op_before_matched_op([zero_index_op])
        new_pointer = create_pointer(id_op.res, zero_index_op.res, rewriter)

        # Get the new state
        new_state = create_state(new_memory_op.res, ub, rewriter)

        # Replace the matched operation
        rewriter.replace_matched_op([], [new_state, new_pointer])


class LowerPointerOffset(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(
        self, op: mem_effect.OffsetPointerOp, rewriter: PatternRewriter
    ):
        # Get the block ID and offset from the pointer
        block_id, offset = get_block_id_and_offset_from_pointer(op.pointer, rewriter)

        # Add the offset to the given offset
        new_offset_op = smt_bv.AddOp(offset, op.offset)
        new_offset_op.res.name_hint = "ptr_offset"
        rewriter.insert_op_before_matched_op([new_offset_op])

        # Create the new pointer
        new_pointer = create_pointer(block_id, new_offset_op.res, rewriter)

        # Replace the matched operation
        rewriter.replace_matched_op([], [new_pointer])


class LowerRead(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: mem_effect.ReadOp, rewriter: PatternRewriter):
        # Unwrap the pointer and the state
        block_id, offset = get_block_id_and_offset_from_pointer(op.pointer, rewriter)
        memory, ub = get_memory_and_ub_from_state(op.state, rewriter)

        # Get the memory block and bytes
        get_block_op = mem.GetBlockOp(memory, block_id)
        block = get_block_op.res
        get_block_bytes_op = mem.GetBlockBytesOp(block)
        bytes = get_block_bytes_op.res
        rewriter.insert_op_before_matched_op([get_block_op, get_block_bytes_op])

        # Check that the offset is within bounds, and update the ub flag
        offset_in_bounds = check_bounds(offset, block, rewriter)
        new_ub_op = smt.OrOp(ub, offset_in_bounds)
        rewriter.insert_op_before_matched_op([new_ub_op])
        ub = new_ub_op.res

        # Read the value in memory
        read_op = mem.ReadBytesOp(bytes, offset, op.res.type)
        rewriter.insert_op_before_matched_op([read_op])

        # Wrap the new state
        new_state = create_state(memory, ub, rewriter)

        # Replace the matched operation
        rewriter.replace_matched_op([], [new_state, read_op.res])


class LowerWrite(RewritePattern):
    @op_type_rewrite_pattern
    def match_and_rewrite(self, op: mem_effect.WriteOp, rewriter: PatternRewriter):
        # Unwrap the pointer and the state
        block_id, offset = get_block_id_and_offset_from_pointer(op.pointer, rewriter)
        memory, ub = get_memory_and_ub_from_state(op.state, rewriter)

        # Get the memory block and bytes
        get_block_op = mem.GetBlockOp(memory, block_id)
        block = get_block_op.res
        get_block_bytes_op = mem.GetBlockBytesOp(block)
        bytes = get_block_bytes_op.res
        rewriter.insert_op_before_matched_op([get_block_op, get_block_bytes_op])

        # Check that the offset is within bounds, and update the ub flag
        offset_in_bounds = check_bounds(offset, block, rewriter)
        new_ub_op = smt.OrOp(ub, offset_in_bounds)
        rewriter.insert_op_before_matched_op([new_ub_op])
        ub = new_ub_op.res

        # Write the value in memory
        write_op = mem.WriteBytesOp(op.value, bytes, offset)
        bytes = write_op.res
        rewriter.insert_op_before_matched_op([write_op])

        # Update the bytes in the block and memory
        set_block_bytes_op = mem.SetBlockBytesOp(block, bytes)
        set_block_op = mem.SetBlockOp(set_block_bytes_op.res, memory, block_id)
        memory = set_block_op.res
        rewriter.insert_op_before_matched_op([set_block_bytes_op, set_block_op])

        # Wrap the new state
        new_state = create_state(memory, ub, rewriter)

        # Replace the matched operation
        rewriter.replace_matched_op([], [new_state])


@dataclass(frozen=True)
class LowerEffectWithMemoryPass(ModulePass):
    name = "lower-effects-with-memory"

    def apply(self, ctx: MLContext, op: ModuleOp) -> None:
        walker = PatternRewriteWalker(
            GreedyRewritePatternApplier(
                [
                    LowerTriggerOp(),
                    LowerToBoolOp(),
                    LowerGenericOp(),
                    LowerAlloc(),
                    LowerPointerOffset(),
                    LowerRead(),
                    LowerWrite(),
                ]
            )
        )
        walker.rewrite_module(op)

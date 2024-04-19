from xdsl.ir import Attribute, Dialect, OpResult
from xdsl.irdl import irdl_op_definition, IRDLOperation, result_def


@irdl_op_definition
class ConstantOp(IRDLOperation):
    name = "smt.synth.constant"

    res: OpResult = result_def()

    def __init__(self, type: Attribute):
        super().__init__(result_types=[type])


SynthDialect = Dialect("smt.synth", [ConstantOp])

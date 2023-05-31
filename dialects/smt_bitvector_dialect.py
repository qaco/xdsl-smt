from __future__ import annotations

from typing import Annotated, TypeVar, IO, overload

from xdsl.dialects.builtin import IntAttr, IntegerAttr, IntegerType

from xdsl.ir import (
    Attribute,
    Dialect,
    OpResult,
    ParametrizedAttribute,
    SSAValue,
    TypeAttribute,
)
from xdsl.irdl import (
    OpAttr,
    Operand,
    ParameterDef,
    irdl_op_definition,
    irdl_attr_definition,
    IRDLOperation,
)
from xdsl.parser import Parser
from xdsl.printer import Printer

from traits.smt_printer import SMTConversionCtx, SMTLibOp, SMTLibSort, SimpleSMTLibOp
from traits.effects import Pure
from dialects.smt_dialect import BoolType


@irdl_attr_definition
class BitVectorType(ParametrizedAttribute, SMTLibSort, TypeAttribute):
    name = "smt.bv.bv"
    width: ParameterDef[IntAttr]

    def print_sort_to_smtlib(self, stream: IO[str]):
        print(f"(_ BitVec {self.width.data})", file=stream, end="")

    def __init__(self, value: int | IntAttr):
        if isinstance(value, int):
            value = IntAttr(value)
        super().__init__([value])

    @staticmethod
    def from_int(value: int) -> BitVectorType:
        return BitVectorType(value)

    @staticmethod
    def parse_parameters(parser: Parser) -> list[Attribute]:
        parser.parse_char("<")
        width = parser.parse_integer()
        parser.parse_char(">")
        return [IntAttr(width)]

    def print_parameters(self, printer: Printer) -> None:
        printer.print("<", self.width.data, ">")


@irdl_attr_definition
class BitVectorValue(ParametrizedAttribute):
    name = "smt.bv.bv_val"

    value: ParameterDef[IntAttr]
    width: ParameterDef[IntAttr]

    def __init__(self, value: int | IntAttr, width: int | IntAttr):
        if isinstance(value, int):
            value = IntAttr(value)
        if isinstance(width, int):
            width = IntAttr(width)
        super().__init__([value, width])

    @staticmethod
    def from_int_value(value: int, width: int = 32) -> BitVectorValue:
        return BitVectorValue(value, width)

    def get_type(self) -> BitVectorType:
        return BitVectorType.from_int(self.width.data)

    def verify(self) -> None:
        if not (0 <= self.value.data < 2**self.width.data):
            raise ValueError("BitVector value out of range")

    def as_smtlib_str(self) -> str:
        return f"(_ bv{self.value.data} {self.width.data})"

    @staticmethod
    def parse_parameters(parser: Parser) -> list[Attribute]:
        parser.parse_char("<")
        value = parser.parse_integer()
        parser.parse_char(":")
        width = parser.parse_integer()
        parser.parse_char(">")
        return [IntAttr(value), IntAttr(width)]

    def print_parameters(self, printer: Printer) -> None:
        printer.print("<", self.value.data, ": ", self.width.data, ">")


@irdl_op_definition
class ConstantOp(IRDLOperation, Pure, SMTLibOp):
    name = "smt.bv.constant"
    value: OpAttr[BitVectorValue]
    res: Annotated[OpResult, BitVectorType]

    @overload
    def __init__(self, value: int | IntAttr, width: int | IntAttr) -> None:
        ...

    @overload
    def __init__(self, value: IntegerAttr[IntegerType]) -> None:
        ...

    def __init__(
        self,
        value: int | IntAttr | IntegerAttr[IntegerType],
        width: int | IntAttr | None = None,
    ) -> None:
        if isinstance(value, int | IntAttr):
            if not isinstance(width, int | IntAttr):
                raise ValueError("Expected width with an `int` value")
            attr = BitVectorValue(value, width)
        else:
            attr = BitVectorValue(value.value, value.typ.width)
        super().__init__(result_types=[attr.get_type()], attributes={"value": attr})

    @staticmethod
    def from_int_value(value: int, width: int) -> ConstantOp:
        bv_value = BitVectorValue.from_int_value(value, width)
        return ConstantOp.create(
            result_types=[bv_value.get_type()], attributes={"value": bv_value}
        )

    def print_expr_to_smtlib(self, stream: IO[str], ctx: SMTConversionCtx) -> None:
        print(self.value.as_smtlib_str(), file=stream, end="")


_UOpT = TypeVar("_UOpT", bound="UnaryBVOp")


class UnaryBVOp(IRDLOperation, Pure):
    res: Annotated[OpResult, BitVectorType]
    arg: Annotated[Operand, BitVectorType]

    @classmethod
    def get(cls: type[_UOpT], arg: SSAValue) -> _UOpT:
        return cls.create(result_types=[arg.typ], operands=[arg])

    def verify_(self):
        if not (self.res.typ == self.arg.typ):
            raise ValueError("Operand and result must have the same type")


_BOpT = TypeVar("_BOpT", bound="BinaryBVOp")


class BinaryBVOp(IRDLOperation, Pure):
    res: Annotated[OpResult, BitVectorType]
    lhs: Annotated[Operand, BitVectorType]
    rhs: Annotated[Operand, BitVectorType]

    def __init__(self, lhs: Operand, rhs: Operand, res: Attribute | None = None):
        if res is None:
            res = lhs.typ
        super().__init__(result_types=[lhs.typ], operands=[lhs, rhs])

    @classmethod
    def get(cls: type[_BOpT], lhs: SSAValue, rhs: SSAValue) -> _BOpT:
        return cls.create(result_types=[lhs.typ], operands=[lhs, rhs])

    def verify_(self):
        if not (self.res.typ == self.lhs.typ == self.rhs.typ):
            raise ValueError("Operands must have same type")


################################################################################
#                          Basic Bitvector Arithmetic                          #
################################################################################


@irdl_op_definition
class AddOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.add"

    def op_name(self) -> str:
        return "bvadd"


@irdl_op_definition
class SubOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.sub"

    def op_name(self) -> str:
        return "bvsub"


@irdl_op_definition
class NegOp(UnaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.neg"

    def op_name(self) -> str:
        return "bvneg"


@irdl_op_definition
class MulOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.mul"

    def op_name(self) -> str:
        return "bvmul"


@irdl_op_definition
class URemOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.urem"

    def op_name(self) -> str:
        return "bvurem"


@irdl_op_definition
class SRemOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.srem"

    def op_name(self) -> str:
        return "bvsrem"


@irdl_op_definition
class SModOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.smod"

    def op_name(self) -> str:
        return "bvsmod"


@irdl_op_definition
class ShlOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.shl"

    def op_name(self) -> str:
        return "bvshl"


@irdl_op_definition
class LShrOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.lshr"

    def op_name(self) -> str:
        return "bvlshr"


@irdl_op_definition
class AShrOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.ashr"

    def op_name(self) -> str:
        return "bvashr"


@irdl_op_definition
class SDivOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.sdiv"

    def op_name(self) -> str:
        return "bvsdiv"


@irdl_op_definition
class UDivOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.udiv"

    def op_name(self) -> str:
        return "bvudiv"


################################################################################
#                                   Bitwise                                    #
################################################################################


@irdl_op_definition
class OrOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.or"

    def op_name(self) -> str:
        return "bvor"


@irdl_op_definition
class AndOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.and"

    def op_name(self) -> str:
        return "bvand"


@irdl_op_definition
class NotOp(UnaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.not"

    def op_name(self) -> str:
        return "bvnot"


@irdl_op_definition
class XorOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.xor"

    def op_name(self) -> str:
        return "bvxor"


@irdl_op_definition
class NAndOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.nand"

    def op_name(self) -> str:
        return "bvnand"


@irdl_op_definition
class NorOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.nor"

    def op_name(self) -> str:
        return "bvnor"


@irdl_op_definition
class XNorOp(BinaryBVOp, SimpleSMTLibOp):
    name = "smt.bv.xnor"

    def op_name(self) -> str:
        return "bvxnor"


################################################################################
#                                  Predicate                                   #
################################################################################

_BPOpT = TypeVar("_BPOpT", bound="BinaryPredBVOp")


class BinaryPredBVOp(IRDLOperation, Pure):
    res: Annotated[OpResult, BoolType]
    lhs: Annotated[Operand, BitVectorType]
    rhs: Annotated[Operand, BitVectorType]

    def __init__(self, lhs: SSAValue, rhs: SSAValue):
        super().__init__(result_types=[BoolType()], operands=[lhs, rhs])

    @classmethod
    def get(cls: type[_BPOpT], lhs: SSAValue, rhs: SSAValue) -> _BPOpT:
        return cls.create(result_types=[BoolType()], operands=[lhs, rhs])

    def verify_(self):
        if not (self.lhs.typ == self.rhs.typ):
            raise ValueError("Operands must have the same type")


@irdl_op_definition
class UleOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.ule"

    def op_name(self) -> str:
        return "bvule"


@irdl_op_definition
class UltOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.ult"

    def op_name(self) -> str:
        return "bvult"


@irdl_op_definition
class UgeOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.uge"

    def op_name(self) -> str:
        return "bvuge"


@irdl_op_definition
class UgtOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.ugt"

    def op_name(self) -> str:
        return "bvugt"


@irdl_op_definition
class SleOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.sle"

    def op_name(self) -> str:
        return "bvsle"


@irdl_op_definition
class SltOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.slt"

    def op_name(self) -> str:
        return "bvslt"


@irdl_op_definition
class SgeOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.sge"

    def op_name(self) -> str:
        return "bvsge"


@irdl_op_definition
class SgtOp(BinaryPredBVOp, SimpleSMTLibOp):
    name = "smt.bv.sgt"

    def op_name(self) -> str:
        return "bvsgt"


SMTBitVectorDialect = Dialect(
    [
        ConstantOp,
        # Arithmetic
        NegOp,
        AddOp,
        SubOp,
        MulOp,
        URemOp,
        SRemOp,
        SModOp,
        ShlOp,
        LShrOp,
        AShrOp,
        UDivOp,
        SDivOp,
        # Bitwise
        NotOp,
        OrOp,
        XorOp,
        AndOp,
        NAndOp,
        NorOp,
        XNorOp,
        # Predicate
        UleOp,
        UltOp,
        UgeOp,
        UgtOp,
        SleOp,
        SltOp,
        SgeOp,
        SgtOp,
    ],
    [BitVectorType, BitVectorValue],
)

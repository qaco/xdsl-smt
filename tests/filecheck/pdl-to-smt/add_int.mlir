// RUN: xdsl-smt "%s" -p=load-int-semantics,pdl-to-smt,lower-effects,canonicalize,dce -t smt | filecheck "%s"

// or(x, y) -> or(y, x)

"builtin.module"() ({
  "pdl.pattern"() ({
    %0 = "pdl.type"() {constantType = i32} : () -> !pdl.type
    %1 = "pdl.operand"(%0) : (!pdl.type) -> !pdl.value
    %2 = "pdl.operand"(%0) : (!pdl.type) -> !pdl.value
    %3 = pdl.operation "arith.addi"(%1, %2 : !pdl.value, !pdl.value) -> (%0 : !pdl.type)
    pdl.rewrite %3 {
      %5 = pdl.operation "arith.subi"(%2, %1 : !pdl.value, !pdl.value) -> (%0 : !pdl.type)
      pdl.replace %3 with %5
    }
  }) {benefit = 1 : i16} : () -> ()
}) : () -> ()

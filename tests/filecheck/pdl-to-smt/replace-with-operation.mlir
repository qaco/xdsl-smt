// RUN: xdsl-smt "%s" -p=pdl-to-smt,lower-effects,canonicalize,dce -t smt | filecheck "%s"

// or(x, y) -> or(y, x)

"builtin.module"() ({
  "pdl.pattern"() ({
    %0 = "pdl.type"() {constantType = i32} : () -> !pdl.type
    %1 = "pdl.operand"(%0) : (!pdl.type) -> !pdl.value
    %2 = "pdl.operand"(%0) : (!pdl.type) -> !pdl.value
    %3 = pdl.operation "arith.ori"(%1, %2 : !pdl.value, !pdl.value) -> (%0 : !pdl.type)
    pdl.rewrite %3 {
      %5 = pdl.operation "arith.ori"(%2, %1 : !pdl.value, !pdl.value) -> (%0 : !pdl.type)
      pdl.replace %3 with %5
    }
  }) {benefit = 1 : i16} : () -> ()
}) : () -> ()


// CHECK:       (declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))
// CHECK-NEXT:  (declare-const tmp Bool)
// CHECK-NEXT:  (declare-const tmp_0 (Pair (_ BitVec 32) Bool))
// CHECK-NEXT:  (declare-const tmp_1 (Pair (_ BitVec 32) Bool))
// CHECK-NEXT:  (assert (not (or tmp (and (not tmp) (=> (not (or (second tmp_0) (second tmp_1))) (and (= (bvor (first tmp_0) (first tmp_1)) (bvor (first tmp_1) (first tmp_0))) (not (or (second tmp_1) (second tmp_0)))))))))
// CHECK-NEXT:  (check-sat)

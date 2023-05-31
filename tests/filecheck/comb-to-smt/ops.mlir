// RUN: xdsl-smt.py %s -p=comb-to-smt,canonicalize-smt -t=smt --split-input-file | filecheck %s

// comb.add

builtin.module {
  "func.func"() ({
  ^0():
    %r = "comb.add"() : () -> i32
    "func.return"(%r) : (i32) -> ()
  }) {"sym_name" = "add_none", "function_type" = () -> i32, "sym_visibility" = "private"} : () -> ()

  // CHECK:      (define-fun {{.*}} () (_ BitVec 32)
  // CHECK-NEXT: (_ bv0 32))

  "func.func"() ({
  ^0(%x: i32):
    %r = "comb.add"(%x) : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) {"sym_name" = "add_one", "function_type" = (i32) -> i32, "sym_visibility" = "private"} : () -> ()

  // CHECK-NEXT: (define-fun {{.*}} ((x (_ BitVec 32))) (_ BitVec 32)
  // CHECK-NEXT:   x)

  "func.func"() ({
  ^0(%x: i32, %y: i32):
    %r = "comb.add"(%x, %y) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) {"sym_name" = "add_two", "function_type" = (i32, i32) -> i32, "sym_visibility" = "private"} : () -> ()

  // CHECK-NEXT: (define-fun {{.*}} ((x_0 (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32)
  // CHECK-NEXT:   (bvadd x_0 y))

  "func.func"() ({
  ^0(%x: i32, %y: i32, %z: i32):
    %r = "comb.add"(%x, %y, %z) : (i32, i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) {"sym_name" = "add_three", "function_type" = (i32, i32, i32) -> i32, "sym_visibility" = "private"} : () -> ()

  // CHECK-NEXT: (define-fun {{.*}} ((x_1 (_ BitVec 32)) (y_0 (_ BitVec 32)) (z (_ BitVec 32))) (_ BitVec 32)
  // CHECK-NEXT: (bvadd (bvadd x_1 y_0) z))

}

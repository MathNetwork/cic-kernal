import Examples.Setup.TreeSetup
open TreeKernel

-- LeanIota.lean
-- Iota reduction: Nat.rec computes on concrete natural numbers

-- Natural number constructors
def zero := Expr.const "Nat.zero" []
def one := Expr.app (.const "Nat.succ" []) zero
def two := Expr.app (.const "Nat.succ" []) one
def three := Expr.app (.const "Nat.succ" []) two

-- whnf only reduces the head -- for full normalization we use defEq
-- (defEq recursively calls whnf on subterms)

-- === Nat.add 0 0 = 0 ===
#eval whnf env5 (.app (.app (.const "Nat.add" []) zero) zero)
-- Expr.const "Nat.zero" []

-- === Nat.add 2 0 = 2 ===
#eval whnf env5 (.app (.app (.const "Nat.add" []) two) zero)
-- succ(succ(zero))

-- === defEq: Nat.add 1 1 = 2 ===
#eval defEq env5 (.app (.app (.const "Nat.add" []) one) one) two
-- true

-- === defEq: Nat.add 2 1 = 3 ===
#eval defEq env5 (.app (.app (.const "Nat.add" []) two) one) three
-- true

-- === defEq: Nat.add 0 0 = 0 ===
#eval defEq env5 (.app (.app (.const "Nat.add" []) zero) zero) zero
-- true

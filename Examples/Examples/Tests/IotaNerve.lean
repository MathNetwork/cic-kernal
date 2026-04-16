import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroIota.lean
-- Iota reduction: Nat.rec computes on concrete natural numbers (hash-based)

-- Natural number constructors
def zero := Expr.const hZero []
def one := Expr.app (.const hSucc []) zero
def two := Expr.app (.const hSucc []) one
def three := Expr.app (.const hSucc []) two

-- === whnf: Nat.add 0 0 = 0 ===
#eval GenericKernel.whnf env5 (.app (.app (.const hNatAdd []) zero) zero)

-- === whnf: Nat.add 2 0 = 2 ===
#eval GenericKernel.whnf env5 (.app (.app (.const hNatAdd []) two) zero)

-- === defEq: Nat.add 1 1 = 2 ===
#eval GenericKernel.defEq env5 (.app (.app (.const hNatAdd []) one) one) two

-- === defEq: Nat.add 2 1 = 3 ===
#eval GenericKernel.defEq env5 (.app (.app (.const hNatAdd []) two) one) three

-- === defEq: Nat.add 0 0 = 0 ===
#eval GenericKernel.defEq env5 (.app (.app (.const hNatAdd []) zero) zero) zero

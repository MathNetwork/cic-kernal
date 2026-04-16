import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroLit.lean
-- Same literal examples using hashes

-- Need String declaration (not in shared setup)
def stringType : Expr := .sort Level.one
def hString : UInt64 := "Sort(Ls(L0))".hash
def litEnv := (check hString stringType none .constructor env1).get!

#eval infer litEnv (.lit (.natVal 42))
#eval infer litEnv (.lit (.strVal "hello"))
#eval defEq litEnv (.lit (.natVal 3)) (.lit (.natVal 3))
#eval defEq litEnv (.lit (.natVal 3)) (.lit (.natVal 4))
#eval whnf litEnv (.lit (.natVal 42))

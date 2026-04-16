import Examples.Setup.TreeSetup
open TreeKernel

-- LeanLit.lean
-- Literal examples

-- Need String declaration (not in shared setup)
def stringType : Expr := .sort Level.one
def litEnv := (check "String" stringType none .constructor env1).get!

-- === infer: natVal has type Nat, strVal has type String ===
#eval infer litEnv (.lit (.natVal 42))
#eval infer litEnv (.lit (.strVal "hello"))

-- === defEq: same literal -> true, different -> false ===
#eval defEq litEnv (.lit (.natVal 3)) (.lit (.natVal 3))
#eval defEq litEnv (.lit (.natVal 3)) (.lit (.natVal 4))

-- === whnf: literals are already in normal form ===
#eval whnf litEnv (.lit (.natVal 42))

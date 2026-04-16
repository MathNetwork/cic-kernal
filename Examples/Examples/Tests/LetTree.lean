import Examples.Setup.TreeSetup
open TreeKernel

-- LeanLet.lean
-- LetE examples: let k : Nat := Nat.zero in k

-- === infer: let k : Nat := zero in k  should have type Nat ===
#eval infer env2 (.letE (.const "Nat" []) (.const "Nat.zero" []) (.bvar 0))
-- expected: some (Const "Nat")

-- === whnf (zeta-reduction): let eliminates to the value ===
#eval whnf env2 (.letE (.const "Nat" []) (.const "Nat.zero" []) (.bvar 0))
-- expected: Const "Nat.zero"

-- === defEq: let expression equals its reduced form ===
#eval defEq env2 (.letE (.const "Nat" []) (.const "Nat.zero" []) (.bvar 0)) (.const "Nat.zero" [])
-- expected: true

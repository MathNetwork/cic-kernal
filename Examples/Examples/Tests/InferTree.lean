import Examples.Setup.TreeSetup
open TreeKernel

-- LeanInfer.lean
-- Type inference examples using TreeKernel with a populated Env

-- === Const: look up registered declarations ===
#eval infer env5 (.const "Nat" [])        -- some (Expr.sort Level.one)
#eval infer env5 (.const "Nat.add" [])    -- some (ForallE (Const "Nat") (ForallE (Const "Nat") (Const "Nat")))
#eval infer env5 (.const "Nat.succ" [])   -- some (ForallE (Const "Nat") (Const "Nat"))

-- === App: function application with known declarations ===
-- Nat.succ applied to a Nat variable
#eval infer env5 (.app (.const "Nat.succ" []) (.bvar 0)) [.const "Nat" []]
-- some (Const "Nat")

-- === Lambda: function that references known declarations ===
-- fun (n : Nat) => Nat.succ n
#eval infer env5 (.lam (.const "Nat" []) (.app (.const "Nat.succ" []) (.bvar 0)))
-- some (ForallE (Const "Nat") (Const "Nat"))

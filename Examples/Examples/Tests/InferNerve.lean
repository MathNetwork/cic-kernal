import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroInfer.lean
-- Type inference examples using HypergraphKernel with a populated AstroNet
-- Same examples as LeanInfer, but Const uses hashes instead of names

-- === Const: look up registered declarations by hash ===
#eval infer env5 (.const hNat [])        -- some (Expr.sort Level.one)
#eval infer env5 (.const hNatAdd [])     -- some (ForallE ...)
#eval infer env5 (.const hSucc [])       -- some (ForallE ...)

-- === App: function application with known declarations ===
-- Nat.succ applied to a Nat variable (using hashes)
#eval infer env5 (.app (.const hSucc []) (.bvar 0)) [.const hNat []]

-- === Lambda: function that references known declarations ===
-- fun (n : Nat) => Nat.succ n (using hashes)
#eval infer env5 (.lam (.const hNat []) (.app (.const hSucc []) (.bvar 0)))

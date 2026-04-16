import Examples.Setup.TreeSetup
open TreeKernel

-- LeanWhnf.lean
-- Weak head normal form reduction examples

-- === beta-reduction: (fun x => x) applied to Sort 0 ===
#eval whnf env5 (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))
-- expected: .sort .zero (lambda eliminated)

-- === delta-reduction: unfold Nat.add definition ===
#eval whnf env5 (.const "Nat.add" [])
-- expected: addValue (unfolds to the lambda expression)

-- === delta does NOT unfold axioms/constructors ===
#eval whnf env5 (.const "Nat" [])
-- expected: .const "Nat" [] (Nat is a constructor, no value to unfold)

#eval whnf env5 (.const "Nat.zero" [])
-- expected: .const "Nat.zero" [] (same -- no value)

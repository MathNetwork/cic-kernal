import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroWhnf.lean
-- Same whnf examples as LeanWhnf, using hashes

-- === beta-reduction: (fun x => x) applied to Sort 0 ===
#eval whnf env5 (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))
-- expected: .sort .zero

-- === delta-reduction: unfold Nat.add definition ===
#eval whnf env5 (.const hNatAdd [])
-- expected: addValue (unfolds to lambda)

-- === delta does NOT unfold constructors ===
#eval whnf env5 (.const hNat [])
-- expected: .const hNat [] (no value to unfold)

#eval whnf env5 (.const hZero [])
-- expected: .const hZero [] (no value)

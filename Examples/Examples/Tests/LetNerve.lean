import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroLet.lean
-- Same LetE examples using hashes

#eval infer env2 (.letE (.const hNat []) (.const hZero []) (.bvar 0))
#eval whnf env2 (.letE (.const hNat []) (.const hZero []) (.bvar 0))
#eval defEq env2 (.letE (.const hNat []) (.const hZero []) (.bvar 0)) (.const hZero [])

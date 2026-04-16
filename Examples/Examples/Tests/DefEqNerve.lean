import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroDefEq.lean
-- Definitional equality examples using HypergraphKernel
-- HypergraphKernel has hash fast path: if hash(a) == hash(b) -> true in O(1)

-- === hash fast path: structurally identical -> same hash -> O(1) true ===
#eval defEq env5 (.sort .zero) (.sort .zero)                    -- true (hash match, no whnf needed)

-- === hash mismatch -> whnf -> structural comparison -> false ===
#eval defEq env5 (.sort .zero) (.sort Level.one)                    -- false

-- === hash mismatch -> whnf -> hash match after reduction -> true ===
-- (fun x => x)(Sort 0) vs Sort 0
-- left hash != right hash, but after whnf both become Sort 0 -> hash match
#eval defEq env5 (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)) (.sort .zero)
-- true

-- === delta-reduction then comparison ===
-- Const(hNatAdd) vs addValue
-- hash(Const) != hash(addValue), whnf unfolds Const, then structural compare
#eval defEq env5 (.const hNatAdd []) addValue               -- true

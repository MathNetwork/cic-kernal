import Examples.Setup.TreeSetup
open TreeKernel

-- LeanDefEq.lean
-- Definitional equality examples using TreeKernel
-- TreeKernel has NO hash fast path -- always whnf then structural comparison

-- === structurally identical -> true ===
#eval defEq env5 (.sort .zero) (.sort .zero)                    -- true

-- === structurally different -> false ===
#eval defEq env5 (.sort .zero) (.sort Level.one)                    -- false

-- === needs beta-reduction to be equal ===
-- (fun x => x)(Sort 0) vs Sort 0
#eval defEq env5 (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)) (.sort .zero)
-- true (left side whnf reduces to Sort 0)

-- === needs delta-reduction to be equal ===
-- Const "Nat.add" vs addValue (the definition body)
#eval defEq env5 (.const "Nat.add" []) addValue             -- true

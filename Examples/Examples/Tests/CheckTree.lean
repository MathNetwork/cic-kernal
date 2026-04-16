import Examples.Setup.TreeSetup
open TreeKernel

-- LeanCheck.lean
-- Register declarations using TreeKernel (name-based): Nat -> Nat.zero -> Nat.succ -> Nat.rec -> Nat.add
-- check flow: infer(value) =?= declaredType -> pass -> register into Env

-- Verify: environment grows by 1 at each step
#eval env1.size  -- 1
#eval env2.size  -- 2
#eval env3.size  -- 3
#eval env4.size  -- 4
#eval env5.size  -- 5

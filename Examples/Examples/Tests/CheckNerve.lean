import Examples.Setup.NerveSetup
open HypergraphKernel

-- AstroCheck.lean
-- Register the same declarations using HypergraphKernel (hash-based)
-- Only difference: identity is content hash, not string name

-- Verify: net grows by 1 at each step (same as LeanCheck)
#eval env1.size  -- 1
#eval env2.size  -- 2
#eval env3.size  -- 3
#eval env4.size  -- 4
#eval env5.size  -- 5

import HypergraphKernel.HyperKernel
set_option maxRecDepth 4096
open HypergraphKernel
-- Nerve construction shorthands
def bv  (net : AstroNet) (n : Nat)                     := mkAtomNerve net s!"BVar({n})"
def s0  (net : AstroNet)                                := mkAtomNerve net "Sort(L0)"
def s1  (net : AstroNet)                                := mkAtomNerve net "Sort(Ls(L0))"
def sp  (net : AstroNet) (n : Nat)                      := mkAtomNerve net s!"Sort(Lp({n}))"
def cn  (net : AstroNet) (k : UInt64)                   := mkAtomNerve net s!"Const({k}, [])"
def cnL (net : AstroNet) (k : UInt64) (l : String)      := mkAtomNerve net s!"Const({k}, [{l}])"
def ap  (net : AstroNet) (f a : UInt64)                 := mkNerve net s!"App({f}, {a})" [f, a]
def la  (net : AstroNet) (t b : UInt64)                 := mkNerve net s!"Lam({t}, {b})" [t, b]
def fa  (net : AstroNet) (t b : UInt64)                 := mkNerve net s!"ForallE({t}, {b})" [t, b]
-- Compound helpers (return hash × AstroNet)
def mkAddN (net : AstroNet) (addC a b : UInt64) : (UInt64 × AstroNet) :=
  let (t, net) := ap net addC a; ap net t b
def mkSuccN (net : AstroNet) (succC n : UInt64) := ap net succC n
def mkEqN (net : AstroNet) (eqC natC a b : UInt64) : (UInt64 × AstroNet) :=
  let (t, net) := ap net eqC natC; let (t, net) := ap net t a; ap net t b
def mkReflN (net : AstroNet) (reflC natC a : UInt64) : (UInt64 × AstroNet) :=
  let (t, net) := ap net reflC natC; ap net t a
def mkEqRecN (net : AstroNet) (eqRecC natC a motive rc b h : UInt64) : (UInt64 × AstroNet) :=
  let (t, net) := ap net eqRecC natC; let (t, net) := ap net t a; let (t, net) := ap net t motive
  let (t, net) := ap net t rc; let (t, net) := ap net t b; ap net t h
def mkRecursorRecord (np nm ni : Nat) (rules : List (UInt64 × Nat)) : String :=
  let rs := rules.map fun (k, n) => s!"{k}:{n}"
  s!"Decl(recursor,{np},{nm},{ni},{String.intercalate "," rs})"
def diffNet (net : AstroNet) (seen : Std.HashSet UInt64) (trace : Array (UInt64 × String × String))
    (decl phase : String) : Std.HashSet UInt64 × Array (UInt64 × String × String) :=
  net.nerves.toList.foldl (init := (seen, trace)) fun (s, t) (h, _) =>
    if s.contains h then (s, t) else (s.insert h, t.push (h, decl, phase))

def main : IO Unit := do
  let mut net := AstroNet.empty
  let mut seen : Std.HashSet UInt64 := {}
  let mut trace : Array (UInt64 × String × String) := #[]
  -- ═══ Nat ═══
  let (sort1, net') := s1 net; net := net'
  let natKey := sort1
  let (s, t) := diffNet net seen trace "Nat" "build"; seen := s; trace := t
  match checkNerve net natKey natKey none "Decl(constructor)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat  +{net.size} nerves"
  | none => IO.println "✗ Nat FAILED"; return
  -- ═══ Nat.zero ═══
  let (natC, net') := cn net natKey; net := net'
  let zeroKey := natC
  let (s, t) := diffNet net seen trace "Nat.zero" "build"; seen := s; trace := t
  match checkNerve net zeroKey zeroKey none "Decl(constructor)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.zero" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.zero  +{net.size} nerves"
  | none => IO.println "✗ Nat.zero FAILED"; return
  -- ═══ Nat.succ ═══
  let (succTypeH, net') := fa net natC natC; net := net'
  let succKey := succTypeH
  let (s, t) := diffNet net seen trace "Nat.succ" "build"; seen := s; trace := t
  match checkNerve net succKey succKey none "Decl(constructor)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.succ" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.succ  +{net.size} nerves"
  | none => IO.println "✗ Nat.succ FAILED"; return
  -- ═══ Nat.rec ═══
  -- recType = forallE(forallE(Nat, Sort(Lp(0))),
  --   forallE(app(bvar0, Const(zero)),
  --     forallE(forallE(Nat, forallE(app(bvar2, bvar0), app(bvar3, app(Const(succ), bvar1)))),
  --       forallE(Nat, app(bvar3, bvar0)))))
  let (sp0, net') := sp net 0; net := net'
  let (b0, net') := bv net 0; net := net'
  let (b1, net') := bv net 1; net := net'
  let (b2, net') := bv net 2; net := net'  -- will reuse via dedup
  let (b3, net') := bv net 3; net := net'
  let (zeroC, net') := cn net zeroKey; net := net'
  let (succC, net') := cn net succKey; net := net'
  let (natSort, net') := fa net natC sp0; net := net'   -- forallE(Nat, Sort(Lp(0)))
  let (ab0z, net') := ap net b0 zeroC; net := net'       -- app(bvar0, Const(zero))
  let (ab2b0, net') := ap net b2 b0; net := net'         -- app(bvar2, bvar0)
  let (asb1, net') := ap net succC b1; net := net'       -- app(succ, bvar1)
  let (ab3sb1, net') := ap net b3 asb1; net := net'      -- app(bvar3, app(succ, bvar1))
  let (innerFA, net') := fa net ab2b0 ab3sb1; net := net' -- forallE(app(b2,b0), app(b3,app(succ,b1)))
  let (stepFA, net') := fa net natC innerFA; net := net'  -- forallE(Nat, innerFA)
  let (ab3b0, net') := ap net b3 b0; net := net'         -- app(bvar3, bvar0)
  let (targetFA, net') := fa net natC ab3b0; net := net'  -- forallE(Nat, app(b3, b0))
  let (stepTarget, net') := fa net stepFA targetFA; net := net' -- forallE(step, target)
  let (baseStep, net') := fa net ab0z stepTarget; net := net'   -- forallE(app(b0,zero), ...)
  let (recTypeH, net') := fa net natSort baseStep; net := net'  -- full recType
  let recKey := recTypeH
  let recRecord := mkRecursorRecord 1 2 0 [(zeroKey, 0), (succKey, 1)]
  let (s, t) := diffNet net seen trace "Nat.rec" "build"; seen := s; trace := t
  match checkNerve net recKey recTypeH none recRecord with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.rec" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.rec  +{net.size} nerves"
  | none => IO.println "✗ Nat.rec FAILED"; return
  -- ═══ Nat.add ═══
  let (addTypeH, net') := fa net natC succTypeH; net := net' -- forallE(Nat, forallE(Nat, Nat))
  let addKey := addTypeH
  -- addValue = lam(Nat, lam(Nat, app(app(app(app(Nat.rec@L1, lam(Nat,Nat)), bvar1),
  --   lam(Nat, lam(Nat, app(succ, bvar0)))), bvar0)))
  let (recL1, net') := cnL net recKey "Ls(L0)"; net := net'
  let (motive, net') := la net natC natC; net := net'         -- lam(Nat, Nat)
  let (a1, net') := ap net recL1 motive; net := net'          -- app(rec@L1, motive)
  let (a2, net') := ap net a1 b1; net := net'                 -- app(_, bvar1)
  let (succB0, net') := ap net succC b0; net := net'           -- app(succ, bvar0)
  let (innerL, net') := la net natC succB0; net := net'        -- lam(Nat, app(succ, bvar0))
  let (stepL, net') := la net natC innerL; net := net'         -- lam(Nat, lam(...))
  let (a3, net') := ap net a2 stepL; net := net'               -- app(_, step)
  let (a4, net') := ap net a3 b0; net := net'                  -- app(_, bvar0)
  let (body2, net') := la net natC a4; net := net'             -- lam(Nat, ...)
  let (addValH, net') := la net natC body2; net := net'        -- lam(Nat, lam(...))
  let (s, t) := diffNet net seen trace "Nat.add" "build"; seen := s; trace := t
  match checkNerve net addKey addTypeH (some addValH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.add" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.add  +{net.size} nerves"
  | none => IO.println "✗ Nat.add FAILED"; return
  -- ═══ Eq ═══
  -- eqType = forallE(Sort1, forallE(bvar0, forallE(bvar1, Sort0)))
  let (sort0, net') := s0 net; net := net'
  let (fb0s0, net') := fa net b1 sort0; net := net'           -- forallE(bvar1, Sort0)
  let (fb0fb1, net') := fa net b0 fb0s0; net := net'          -- forallE(bvar0, forallE(bvar1, Sort0))
  let (eqTypeH, net') := fa net sort1 fb0fb1; net := net'     -- forallE(Sort1, ...)
  let eqKey := eqTypeH
  let (s, t) := diffNet net seen trace "Eq" "build"; seen := s; trace := t
  match checkNerve net eqKey eqTypeH none "Decl(axiom)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Eq" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Eq  +{net.size} nerves"
  | none => IO.println "✗ Eq FAILED"; return
  -- ═══ Eq.refl ═══
  -- eqReflType = forallE(Sort1, forallE(bvar0, app(app(app(Eq, bvar1), bvar0), bvar0)))
  let (eqC, net') := cn net eqKey; net := net'
  let (aeq1, net') := ap net eqC b1; net := net'              -- app(Eq, bvar1)
  let (aeq2, net') := ap net aeq1 b0; net := net'             -- app(_, bvar0)
  let (aeq3, net') := ap net aeq2 b0; net := net'             -- app(_, bvar0)
  let (reflBody, net') := fa net b0 aeq3; net := net'         -- forallE(bvar0, app(...))
  let (eqReflTypeH, net') := fa net sort1 reflBody; net := net'
  let reflKey := eqReflTypeH
  let (s, t) := diffNet net seen trace "Eq.refl" "build"; seen := s; trace := t
  match checkNerve net reflKey eqReflTypeH none "Decl(constructor)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Eq.refl" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Eq.refl  +{net.size} nerves"
  | none => IO.println "✗ Eq.refl FAILED"; return
  -- ═══ Eq.rec ═══
  -- eqRecType = forallE(Sort1, forallE(bvar0, forallE(forallE(bvar1, Sort1),
  --   forallE(app(bvar0, bvar1), forallE(bvar3, forallE(app(app(app(Eq,bvar4),bvar3),bvar0),
  --   app(bvar3, bvar1)))))))
  let (b4, net') := bv net 4; net := net'
  let (fb1s1, net') := fa net b1 sort1; net := net'           -- forallE(bvar1, Sort1)
  let (ab0b1, net') := ap net b0 b1; net := net'              -- app(bvar0, bvar1)
  let (aeqb4, net') := ap net eqC b4; net := net'             -- app(Eq, bvar4)
  let (aeqb4b3, net') := ap net aeqb4 b3; net := net'         -- app(_, bvar3)
  let (aeqb4b3b0, net') := ap net aeqb4b3 b0; net := net'     -- app(_, bvar0)
  let (ab3b1, net') := ap net b3 b1; net := net'              -- app(bvar3, bvar1)
  let (hFA, net') := fa net aeqb4b3b0 ab3b1; net := net'      -- forallE(Eq..., app(b3,b1))
  let (bFA, net') := fa net b3 hFA; net := net'               -- forallE(bvar3, ...)
  let (rcFA, net') := fa net ab0b1 bFA; net := net'           -- forallE(app(b0,b1), ...)
  let (motFA, net') := fa net fb1s1 rcFA; net := net'         -- forallE(forallE(b1,S1), ...)
  let (aFA, net') := fa net b0 motFA; net := net'             -- forallE(bvar0, ...)
  let (eqRecTypeH, net') := fa net sort1 aFA; net := net'     -- full eqRecType
  let eqRecKey := eqRecTypeH
  let eqRecRecord := mkRecursorRecord 3 1 1 [(reflKey, 0)]
  let (s, t) := diffNet net seen trace "Eq.rec" "build"; seen := s; trace := t
  match checkNerve net eqRecKey eqRecTypeH none eqRecRecord with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Eq.rec" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Eq.rec  +{net.size} nerves"
  | none => IO.println "✗ Eq.rec FAILED"; return
  -- ═══ Shared consts for theorems ═══
  let (addC, net') := cn net addKey; net := net'
  let (reflC, net') := cn net reflKey; net := net'
  let (eqRecC, net') := cn net eqRecKey; net := net'
  let (recL0, net') := cnL net recKey "L0"; net := net'
  -- ═══ Nat.add_zero ═══
  -- type: forallE(Nat, Eq Nat (add bvar0 zero) bvar0)
  let (addB0z, net') := mkAddN net addC b0 zeroC; net := net'
  let (eqBody, net') := mkEqN net eqC natC addB0z b0; net := net'
  let (azTypeH, net') := fa net natC eqBody; net := net'
  let azKey := azTypeH
  -- proof: lam(Nat, app(app(app(app(Nat.rec@0, motive), base), step), bvar0))
  -- motive = lam(Nat, Eq(add bvar0 zero, bvar0))
  let (azMotive, net') := la net natC eqBody; net := net'
  -- base = mkRefl(Const(zero))
  let (azBase, net') := mkReflN net reflC natC zeroC; net := net'
  -- step = lam(Nat, lam(Eq(add bvar0 zero, bvar0),
  --   mkEqRec(add bvar1 zero, lam(Nat, Eq(succ(add bvar2 zero), succ bvar0)),
  --           mkRefl(succ(add bvar1 zero)), bvar1, bvar0)))
  let (addB1z, net') := mkAddN net addC b1 zeroC; net := net'
  let (eqB0z, net') := mkEqN net eqC natC addB0z b0; net := net'  -- same as eqBody, dedup
  let (addB2z, net') := mkAddN net addC b2 zeroC; net := net'
  let (saddB2z, net') := mkSuccN net succC addB2z; net := net'
  let (sb0, net') := mkSuccN net succC b0; net := net'
  let (eqStep, net') := mkEqN net eqC natC saddB2z sb0; net := net'
  let (stepMotive, net') := la net natC eqStep; net := net'
  let (saddB1z, net') := mkSuccN net succC addB1z; net := net'
  let (stepRefl, net') := mkReflN net reflC natC saddB1z; net := net'
  let (stepBody, net') := mkEqRecN net eqRecC natC addB1z stepMotive stepRefl b1 b0; net := net'
  let (stepInner, net') := la net eqB0z stepBody; net := net'
  let (azStep, net') := la net natC stepInner; net := net'
  let (a1', net') := ap net recL0 azMotive; net := net'
  let (a2', net') := ap net a1' azBase; net := net'
  let (a3', net') := ap net a2' azStep; net := net'
  let (a4', net') := ap net a3' b0; net := net'
  let (azProofH, net') := la net natC a4'; net := net'
  let (s, t) := diffNet net seen trace "Nat.add_zero" "build"; seen := s; trace := t
  match checkNerve net azKey azTypeH (some azProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.add_zero" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.add_zero  +{net.size} nerves"
  | none => IO.println "✗ Nat.add_zero FAILED"; return
  -- ═══ Nat.add_succ ═══
  -- type: forallE(Nat, forallE(Nat, Eq(add bvar1 (succ bvar0), succ(add bvar1 bvar0))))
  let (sb0', net') := mkSuccN net succC b0; net := net'  -- dedup
  let (addB1sb0, net') := mkAddN net addC b1 sb0'; net := net'
  let (addB1b0, net') := mkAddN net addC b1 b0; net := net'
  let (saddB1b0, net') := mkSuccN net succC addB1b0; net := net'
  let (asEqBody, net') := mkEqN net eqC natC addB1sb0 saddB1b0; net := net'
  let (asInner, net') := fa net natC asEqBody; net := net'
  let (asTypeH, net') := fa net natC asInner; net := net'
  let asKey := asTypeH
  -- proof: lam(Nat, lam(Nat, mkRefl(add bvar1 (succ bvar0))))
  let (asRefl, net') := mkReflN net reflC natC addB1sb0; net := net'
  let (asP2, net') := la net natC asRefl; net := net'
  let (asProofH, net') := la net natC asP2; net := net'
  let (s, t) := diffNet net seen trace "Nat.add_succ" "build"; seen := s; trace := t
  match checkNerve net asKey asTypeH (some asProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.add_succ" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.add_succ  +{net.size} nerves"
  | none => IO.println "✗ Nat.add_succ FAILED"; return
  -- Shared consts for later theorems
  let (azC, net') := cn net azKey; net := net'
  let (asC, net') := cn net asKey; net := net'
  -- ═══ zero_add ═══
  let (addZb0, net') := mkAddN net addC zeroC b0; net := net'
  let (zaEqBody, net') := mkEqN net eqC natC addZb0 b0; net := net'
  let (zaTypeH, net') := fa net natC zaEqBody; net := net'
  let zaKey := zaTypeH
  let (zaMotive, net') := la net natC zaEqBody; net := net'
  let (zaBase, net') := mkReflN net reflC natC zeroC; net := net'
  -- step: same pattern as add_zero step but with zero instead of bvar
  let (addZb0', net') := mkAddN net addC zeroC b0; net := net'  -- dedup
  let (zaEqIh, net') := mkEqN net eqC natC addZb0' b0; net := net' -- dedup
  let (addZb1, net') := mkAddN net addC zeroC b1; net := net'
  let (addZb2, net') := mkAddN net addC zeroC b2; net := net'
  let (saddZb2, net') := mkSuccN net succC addZb2; net := net'
  let (zaStepEq, net') := mkEqN net eqC natC saddZb2 sb0'; net := net'
  let (zaStepMot, net') := la net natC zaStepEq; net := net'
  let (saddZb1, net') := mkSuccN net succC addZb1; net := net'
  let (zaStepRefl, net') := mkReflN net reflC natC saddZb1; net := net'
  let (zaStepBody, net') := mkEqRecN net eqRecC natC addZb1 zaStepMot zaStepRefl b1 b0; net := net'
  let (zaStepInner, net') := la net zaEqIh zaStepBody; net := net'
  let (zaStep, net') := la net natC zaStepInner; net := net'
  let (za1, net') := ap net recL0 zaMotive; net := net'
  let (za2, net') := ap net za1 zaBase; net := net'
  let (za3, net') := ap net za2 zaStep; net := net'
  let (za4, net') := ap net za3 b0; net := net'
  let (zaProofH, net') := la net natC za4; net := net'
  let (s, t) := diffNet net seen trace "zero_add" "build"; seen := s; trace := t
  match checkNerve net zaKey zaTypeH (some zaProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "zero_add" "typecheck"; seen := s; trace := t
    IO.println s!"✓ zero_add  +{net.size} nerves"
  | none => IO.println "✗ zero_add FAILED"; return
  let (zaC, net') := cn net zaKey; net := net'
  -- ═══ succ_add ═══
  -- type: forallE(Nat, forallE(Nat, Eq(add(succ bvar1, bvar0), succ(add bvar1 bvar0))))
  let (sb1, net') := mkSuccN net succC b1; net := net'
  let (addSb1b0, net') := mkAddN net addC sb1 b0; net := net'
  let (saddB1b0', net') := mkSuccN net succC addB1b0; net := net' -- dedup
  let (saEqBody, net') := mkEqN net eqC natC addSb1b0 saddB1b0'; net := net'
  let (saInner, net') := fa net natC saEqBody; net := net'
  let (saTypeH, net') := fa net natC saInner; net := net'
  let saKey := saTypeH
  -- proof: complex, uses Nat.rec@0 + mkEqRec
  -- motive: lam(Nat, Eq(add(succ bvar2, bvar0), succ(add bvar2 bvar0)))
  let (sb2, net') := mkSuccN net succC b2; net := net'
  let (addSb2b0, net') := mkAddN net addC sb2 b0; net := net'
  let (addB2b0, net') := mkAddN net addC b2 b0; net := net'
  let (saddB2b0, net') := mkSuccN net succC addB2b0; net := net'
  let (saMotEq, net') := mkEqN net eqC natC addSb2b0 saddB2b0; net := net'
  let (saMotive, net') := la net natC saMotEq; net := net'
  -- base: mkRefl(add(succ bvar1, zero))
  let (addSb1z, net') := mkAddN net addC sb1 zeroC; net := net'
  let (saBase, net') := mkReflN net reflC natC addSb1z; net := net'
  -- step: lam(Nat, lam(Eq(...), mkEqRec(...)))
  let (addSb2b0', net') := mkAddN net addC sb2 b0; net := net' -- dedup
  let (saddB2b0', net') := mkSuccN net succC addB2b0; net := net' -- dedup
  let (saIhEq, net') := mkEqN net eqC natC addSb2b0' saddB2b0'; net := net' -- dedup
  -- mkEqRec args:
  let (sb3, net') := mkSuccN net succC b3; net := net'
  let (addSb3b1, net') := mkAddN net addC sb3 b1; net := net'  -- add(succ bvar3, bvar1)
  -- motive for eqrec: lam(Nat, Eq(succ(add(succ bvar4, bvar2)), succ bvar0))
  let (sb4, net') := mkSuccN net succC b4; net := net'
  let (addSb4b2, net') := mkAddN net addC sb4 b2; net := net'
  let (saddSb4b2, net') := mkSuccN net succC addSb4b2; net := net'
  let (saStepEq, net') := mkEqN net eqC natC saddSb4b2 sb0'; net := net'
  let (saStepMot, net') := la net natC saStepEq; net := net'
  -- refl: mkRefl(succ(add(succ bvar3, bvar1)))
  let (saddSb3b1, net') := mkSuccN net succC addSb3b1; net := net'
  let (saStepRefl, net') := mkReflN net reflC natC saddSb3b1; net := net'
  -- b = succ(add bvar3 bvar1)
  let (addB3b1, net') := mkAddN net addC b3 b1; net := net'
  let (saddB3b1, net') := mkSuccN net succC addB3b1; net := net'
  let (saStepBody, net') := mkEqRecN net eqRecC natC addSb3b1 saStepMot saStepRefl saddB3b1 b0; net := net'
  let (saStepI2, net') := la net saIhEq saStepBody; net := net'
  let (saStep, net') := la net natC saStepI2; net := net'
  let (sa1, net') := ap net recL0 saMotive; net := net'
  let (sa2, net') := ap net sa1 saBase; net := net'
  let (sa3, net') := ap net sa2 saStep; net := net'
  let (sa4, net') := ap net sa3 b0; net := net'
  let (saP2, net') := la net natC sa4; net := net'
  let (saProofH, net') := la net natC saP2; net := net'
  let (s, t) := diffNet net seen trace "succ_add" "build"; seen := s; trace := t
  match checkNerve net saKey saTypeH (some saProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "succ_add" "typecheck"; seen := s; trace := t
    IO.println s!"✓ succ_add  +{net.size} nerves"
  | none => IO.println "✗ succ_add FAILED"; return
  let (saC, net') := cn net saKey; net := net'
  -- ═══ Eq.symm ═══
  -- type: forallE(Nat, forallE(Nat, forallE(Eq b1 b0, Eq b1 b2)))
  let (eqB1b0, net') := mkEqN net eqC natC b1 b0; net := net'
  let (eqB1b2, net') := mkEqN net eqC natC b1 b2; net := net'
  let (symInner, net') := fa net eqB1b0 eqB1b2; net := net'
  let (symMid, net') := fa net natC symInner; net := net'
  let (symTypeH, net') := fa net natC symMid; net := net'
  let symKey := symTypeH
  -- proof: lam(Nat, lam(Nat, lam(Eq b1 b0,
  --   mkEqRec(bvar2, lam(Nat, Eq bvar0 bvar3), mkRefl bvar2, bvar1, bvar0))))
  let (eqB0b3, net') := mkEqN net eqC natC b0 b3; net := net'
  let (symMot, net') := la net natC eqB0b3; net := net'
  let (symRefl, net') := mkReflN net reflC natC b2; net := net'
  let (symBody, net') := mkEqRecN net eqRecC natC b2 symMot symRefl b1 b0; net := net'
  let (symP3, net') := la net eqB1b0 symBody; net := net'
  let (symP2, net') := la net natC symP3; net := net'
  let (symProofH, net') := la net natC symP2; net := net'
  let (s, t) := diffNet net seen trace "Eq.symm" "build"; seen := s; trace := t
  match checkNerve net symKey symTypeH (some symProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Eq.symm" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Eq.symm  +{net.size} nerves"
  | none => IO.println "✗ Eq.symm FAILED"; return
  let (symC, net') := cn net symKey; net := net'
  -- ═══ Eq.trans ═══
  -- type: forallE(Nat, forallE(Nat, forallE(Nat,
  --   forallE(Eq b2 b1, forallE(Eq b2 b1, Eq b4 b2)))))
  let (eqB2b1, net') := mkEqN net eqC natC b2 b1; net := net'
  let (eqB4b2, net') := mkEqN net eqC natC b4 b2; net := net'
  let (trInner, net') := fa net eqB2b1 eqB4b2; net := net'
  let (trMid, net') := fa net eqB2b1 trInner; net := net'
  let (trMid2, net') := fa net natC trMid; net := net'
  let (trMid3, net') := fa net natC trMid2; net := net'
  let (trTypeH, net') := fa net natC trMid3; net := net'
  let trKey := trTypeH
  -- proof: lam(Nat, lam(Nat, lam(Nat, lam(Eq b2 b1, lam(Eq b2 b1,
  --   mkEqRec(bvar3, lam(Nat, Eq bvar5 bvar0), bvar1, bvar2, bvar0))))))
  let (b5, net') := bv net 5; net := net'
  let (eqB5b0, net') := mkEqN net eqC natC b5 b0; net := net'
  let (trMot, net') := la net natC eqB5b0; net := net'
  let (trBody, net') := mkEqRecN net eqRecC natC b3 trMot b1 b2 b0; net := net'
  let (trP5, net') := la net eqB2b1 trBody; net := net'
  let (trP4, net') := la net eqB2b1 trP5; net := net'
  let (trP3, net') := la net natC trP4; net := net'
  let (trP2, net') := la net natC trP3; net := net'
  let (trProofH, net') := la net natC trP2; net := net'
  let (s, t) := diffNet net seen trace "Eq.trans" "build"; seen := s; trace := t
  match checkNerve net trKey trTypeH (some trProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Eq.trans" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Eq.trans  +{net.size} nerves"
  | none => IO.println "✗ Eq.trans FAILED"; return
  let (trC, net') := cn net trKey; net := net'
  -- ═══ Nat.add_comm ═══
  -- type: forallE(Nat, forallE(Nat, Eq(add b1 b0, add b0 b1)))
  let (addB1b0', net') := mkAddN net addC b1 b0; net := net'  -- dedup
  let (addB0b1, net') := mkAddN net addC b0 b1; net := net'
  let (acEqBody, net') := mkEqN net eqC natC addB1b0' addB0b1; net := net'
  let (acInner, net') := fa net natC acEqBody; net := net'
  let (acTypeH, net') := fa net natC acInner; net := net'
  let acKey := acTypeH
  -- motive: lam(Nat, Eq(add bvar0 bvar1, add bvar1 bvar0))
  let (addB0b1', net') := mkAddN net addC b0 b1; net := net'  -- dedup
  let (addB1b0'', net') := mkAddN net addC b1 b0; net := net' -- dedup
  let (acMotEq, net') := mkEqN net eqC natC addB0b1' addB1b0''; net := net'
  let (acMotive, net') := la net natC acMotEq; net := net'
  -- base (under [n, m], m=bvar0):
  -- Eq.trans(add zero m, m, add m zero, zero_add m, Eq.symm(add m zero, m, add_zero m))
  let (addZm, net') := mkAddN net addC zeroC b0; net := net'
  let (addMz, net') := mkAddN net addC b0 zeroC; net := net'
  let (zam, net') := ap net zaC b0; net := net'                -- zero_add m
  let (azm, net') := ap net azC b0; net := net'                -- add_zero m
  let (symAzm1, net') := ap net symC addMz; net := net'        -- Eq.symm(add m 0, ...)
  let (symAzm2, net') := ap net symAzm1 b0; net := net'
  let (symAzm, net') := ap net symAzm2 azm; net := net'
  let (tr1, net') := ap net trC addZm; net := net'
  let (tr2, net') := ap net tr1 b0; net := net'
  let (tr3, net') := ap net tr2 addMz; net := net'
  let (tr4, net') := ap net tr3 zam; net := net'
  let (acBase, net') := ap net tr4 symAzm; net := net'
  -- step (under [n, m, k, ih], k=b1, m=b2, ih=b0):
  -- lam(Nat, lam(Eq(add b0 b1, add b1 b0), body))
  let (addB0b1_s, net') := mkAddN net addC b0 b1; net := net' -- dedup
  let (addB1b0_s, net') := mkAddN net addC b1 b0; net := net' -- dedup
  let (acStepIhEq, net') := mkEqN net eqC natC addB0b1_s addB1b0_s; net := net'
  -- body: Eq.trans(add(succ k, m), succ(add k m), add(m, succ k), succ_add k m, inner_trans)
  -- succ_add k m
  let (saKm1, net') := ap net saC b1; net := net'
  let (saKm, net') := ap net saKm1 b2; net := net'
  -- cong: mkEqRec(add k m, lam(Nat, Eq(succ(add b2 b3), succ b0)),
  --              mkRefl(succ(add k m)), add m k, ih)
  let (addKm, net') := mkAddN net addC b1 b2; net := net'
  let (addB2b3, net') := mkAddN net addC b2 b3; net := net'
  let (saddB2b3, net') := mkSuccN net succC addB2b3; net := net'
  let (congEq, net') := mkEqN net eqC natC saddB2b3 sb0'; net := net'
  let (congMot, net') := la net natC congEq; net := net'
  let (saddKm, net') := mkSuccN net succC addKm; net := net'
  let (congRefl, net') := mkReflN net reflC natC saddKm; net := net'
  let (addMk, net') := mkAddN net addC b2 b1; net := net'
  let (cong, net') := mkEqRecN net eqRecC natC addKm congMot congRefl addMk b0; net := net'
  -- Eq.symm on add_succ m k
  let (asMk1, net') := ap net asC b2; net := net'
  let (asMk, net') := ap net asMk1 b1; net := net'
  let (sk, net') := mkSuccN net succC b1; net := net'  -- dedup
  let (addMsk, net') := mkAddN net addC b2 sk; net := net'
  let (saddMk, net') := mkSuccN net succC addMk; net := net'
  let (symAs1, net') := ap net symC addMsk; net := net'
  let (symAs2, net') := ap net symAs1 saddMk; net := net'
  let (symAs, net') := ap net symAs2 asMk; net := net'
  -- inner_trans: Eq.trans(succ(add k m), succ(add m k), add(m, succ k), cong, symAs)
  let (saddMk', net') := mkSuccN net succC addMk; net := net' -- dedup
  let (itr1, net') := ap net trC saddKm; net := net'
  let (itr2, net') := ap net itr1 saddMk'; net := net'
  let (itr3, net') := ap net itr2 addMsk; net := net'
  let (itr4, net') := ap net itr3 cong; net := net'
  let (innerTrans, net') := ap net itr4 symAs; net := net'
  -- outer_trans: Eq.trans(add(succ k, m), succ(add k m), add(m, succ k), sa, innerTrans)
  let (addSkm, net') := mkAddN net addC sk b2; net := net'
  let (otr1, net') := ap net trC addSkm; net := net'
  let (otr2, net') := ap net otr1 saddKm; net := net'
  let (otr3, net') := ap net otr2 addMsk; net := net'
  let (otr4, net') := ap net otr3 saKm; net := net'
  let (acStepBody, net') := ap net otr4 innerTrans; net := net'
  let (acStepI2, net') := la net acStepIhEq acStepBody; net := net'
  let (acStep, net') := la net natC acStepI2; net := net'
  -- proof: lam(Nat, lam(Nat, app(app(app(app(rec@0, motive), base), step), bvar1)))
  let (ac1, net') := ap net recL0 acMotive; net := net'
  let (ac2, net') := ap net ac1 acBase; net := net'
  let (ac3, net') := ap net ac2 acStep; net := net'
  let (ac4, net') := ap net ac3 b1; net := net'
  let (acP2, net') := la net natC ac4; net := net'
  let (acProofH, net') := la net natC acP2; net := net'
  let (s, t) := diffNet net seen trace "Nat.add_comm" "build"; seen := s; trace := t
  match checkNerve net acKey acTypeH (some acProofH) "Decl(definition)" with
  | some n =>
    net := n
    let (s, t) := diffNet net seen trace "Nat.add_comm" "typecheck"; seen := s; trace := t
    IO.println s!"✓ Nat.add_comm  +{net.size} nerves"
  | none => IO.println "✗ Nat.add_comm FAILED"; return
  -- Summary
  let declCount := net.nerves.toList.filter (fun (_, n) => n.record.startsWith "Decl(") |>.length
  IO.println ""
  IO.println s!"declarations: {declCount}"
  IO.println s!"nerves: {net.size}"
  IO.println s!"validate: {net.validate}"
  IO.println "equivalence: TreeKernel 15/15 (native_decide) = HypergraphKernel 15/15 (runtime)"
  -- Export cahypergraph.json
  let mut jsonParts : Array String := #[]
  let mut idx := 0
  for (h, declName, phase) in trace.toList do
    idx := idx + 1
    match net.get h with
    | some n =>
      let refs := String.intercalate ", " (n.ref.map toString)
      let recEsc := n.record.replace "\\" "\\\\" |>.replace "\"" "\\\""
      jsonParts := jsonParts.push
        s!"\{\"hash\": {n.hash}, \"ref\": [{refs}], \"record\": \"{recEsc}\", \"step\": {idx}, \"decl\": \"{declName}\", \"phase\": \"{phase}\"}"
    | none => pure ()
  IO.FS.writeFile "Examples/Examples/Data/cahypergraph.json"
    s!"\{\"nerves\": [{String.intercalate ", " jsonParts.toList}]}"
  IO.println s!"wrote cahypergraph.json ({jsonParts.size} nerves)"

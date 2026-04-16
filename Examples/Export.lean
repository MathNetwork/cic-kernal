import Examples.Setup.NerveSetup
import Examples.Tests.EqNerve
open HypergraphKernel

def hashToName (h : UInt64) : String :=
  let ns : List (UInt64 × String) := [
    (hNat, "Nat"), (hZero, "Nat.zero"), (hSucc, "Nat.succ"), (hRec, "Nat.rec"),
    (hNatAdd, "Nat.add"), (hEq, "Eq"), (hEqRefl, "Eq.refl"), (hEqRec, "Eq.rec"),
    (hAddZero, "Nat.add_zero"), (hAddSucc, "Nat.add_succ"), (hZeroAdd, "zero_add"),
    (hSuccAdd, "succ_add"), (hEqSymm, "Eq.symm"), (hEqTrans, "Eq.trans"),
    (hAddComm, "Nat.add_comm")]
  match ns.find? (fun p => p.1 == h) with | some (_, n) => n | none => s!"{h}"

/-- Convert Level to string. -/
partial def levelStr : Level → String
  | .zero => "0"
  | .succ l => s!"S({levelStr l})"
  | .max l1 l2 => s!"max({levelStr l1},{levelStr l2})"
  | .imax l1 l2 => s!"imax({levelStr l1},{levelStr l2})"
  | .param n => s!"p{n}"

/-- Convert Expr to nested JSON with hash and post-order step. Returns (json, nextStep, thisStep). -/
partial def exprToJson (e : Expr) (step : Nat) : (String × Nat × Nat) :=
  let h := (hashExpr e).1
  match e with
  | .bvar n =>
    let s := step + 1
    (s!"\{\"tag\":\"BVar\",\"hash\":{h},\"step\":{s},\"index\":{n},\"children\":[]}", s, s)
  | .sort u =>
    let s := step + 1
    (s!"\{\"tag\":\"Sort\",\"hash\":{h},\"step\":{s},\"level\":\"{levelStr u}\",\"children\":[]}", s, s)
  | .const k levels =>
    let name := hashToName k
    let ls := levels.map (fun l => s!"\"{levelStr l}\"")
    let s := step + 1
    (s!"\{\"tag\":\"Const\",\"hash\":{h},\"step\":{s},\"name\":\"{name}\",\"levels\":[{String.intercalate "," ls}],\"children\":[]}", s, s)
  | .lit l =>
    let v := match l with | .natVal n => s!"{n}" | .strVal s => s!"\"{s}\""
    let s := step + 1
    (s!"\{\"tag\":\"Lit\",\"hash\":{h},\"step\":{s},\"value\":{v},\"children\":[]}", s, s)
  | .app f a =>
    let (fj, s1, _) := exprToJson f step
    let (aj, s2, _) := exprToJson a s1
    let s := s2 + 1
    (s!"\{\"tag\":\"App\",\"hash\":{h},\"step\":{s},\"children\":[{fj},{aj}]}", s, s)
  | .lam ty body =>
    let (tj, s1, _) := exprToJson ty step
    let (bj, s2, _) := exprToJson body s1
    let s := s2 + 1
    (s!"\{\"tag\":\"Lam\",\"hash\":{h},\"step\":{s},\"children\":[{tj},{bj}]}", s, s)
  | .forallE ty body =>
    let (tj, s1, _) := exprToJson ty step
    let (bj, s2, _) := exprToJson body s1
    let s := s2 + 1
    (s!"\{\"tag\":\"ForallE\",\"hash\":{h},\"step\":{s},\"children\":[{tj},{bj}]}", s, s)
  | .letE ty val body =>
    let (tj, s1, _) := exprToJson ty step
    let (vj, s2, _) := exprToJson val s1
    let (bj, s3, _) := exprToJson body s2
    let s := s3 + 1
    (s!"\{\"tag\":\"LetE\",\"hash\":{h},\"step\":{s},\"children\":[{tj},{vj},{bj}]}", s, s)

def kindJ : DeclKind → String
  | .axiom => "axiom" | .constructor => "constructor"
  | .recursor _ => "recursor" | .definition => "definition"

structure Ent where
  ename : String
  ekey  : UInt64
  ekind : DeclKind
  ety   : Expr
  eval  : Option Expr

def entries : List Ent := [
  ⟨"Nat",          hNat,     .constructor, natType,     none⟩,
  ⟨"Nat.zero",     hZero,    .constructor, zeroType,    none⟩,
  ⟨"Nat.succ",     hSucc,    .constructor, succType,    none⟩,
  ⟨"Nat.rec",      hRec,     .recursor natRecInfo, recType, none⟩,
  ⟨"Nat.add",      hNatAdd,  .definition,  addType,     some addValue⟩,
  ⟨"Eq",           hEq,      .axiom,       eqType,      none⟩,
  ⟨"Eq.refl",      hEqRefl,  .constructor, eqReflType,  none⟩,
  ⟨"Eq.rec",       hEqRec,   .recursor eqRecInfo, eqRecType, none⟩,
  ⟨"Nat.add_zero", hAddZero, .definition,  addZeroType, some addZeroProof⟩,
  ⟨"Nat.add_succ", hAddSucc, .definition,  addSuccType, some addSuccProof⟩,
  ⟨"zero_add",     hZeroAdd, .definition,  zeroAddType, some zeroAddProof⟩,
  ⟨"succ_add",     hSuccAdd, .definition,  succAddType, some succAddProof⟩,
  ⟨"Eq.symm",      hEqSymm,  .definition,  eqSymmType,  some eqSymmProof⟩,
  ⟨"Eq.trans",     hEqTrans, .definition,  eqTransType, some eqTransProof⟩,
  ⟨"Nat.add_comm", hAddComm, .definition,  addCommType, some addCommProof⟩]

def main : IO Unit := do
  let mut declJsons : Array String := #[]

  for e in entries do
    let (typeJson, _, _) := exprToJson e.ety 0
    let valueJson := match e.eval with
      | some val => (exprToJson val 0).1
      | none => "null"
    declJsons := declJsons.push
      s!"\{\"name\":\"{e.ename}\",\"kind\":\"{kindJ e.ekind}\",\"type\":{typeJson},\"value\":{valueJson}}"
    IO.println s!"✓ {e.ename}"

  IO.FS.writeFile "Examples/Examples/Data/treeenv.json"
    s!"\{\"declarations\":[{String.intercalate "," declJsons.toList}]}"
  IO.println s!"wrote treeenv.json ({declJsons.size} declarations)"

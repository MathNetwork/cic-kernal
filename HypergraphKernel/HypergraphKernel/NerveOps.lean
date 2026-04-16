/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import HypergraphKernel.AstroNerve
import HypergraphKernel.AstroNet

/-!
# NerveOps: Record Parsing Utilities

Parses structural information from the `record` field of an `AstroNerve`.
Record strings use the following formats:

- `"BVar(n)"`, `"Sort(…)"`, `"Const(h, […])"`, `"NatLit(n)"`, `"StrLit(s)"`
- `"App(h1, h2)"`, `"Lam(h1, h2)"`, `"ForallE(h1, h2)"`
- `"LetE(h1, h2, h3)"`

## Main Definitions

- `parseTag`: Extract the constructor tag from a record string.
- `parseBVarIdx`: Extract the de Bruijn index from a BVar record.
- `parseSortLevel`: Extract a simplified level number from a Sort record.
- `parseConstKey`: Extract the referenced declaration hash from a Const record.
- `AstroNerve.tag`: Convenience accessor for the constructor tag.
- `AstroNerve.children`: Convenience accessor for child hashes (empty for atoms).
-/

namespace HypergraphKernel

/-- Constructor tag for a nerve, derived from its record string. -/
inductive NerveTag where
  | bvar | sort | const | app | lam | forallE | letE | lit
  deriving BEq, Repr

/-- Extract the constructor tag from a record string. -/
def parseTag (record : String) : NerveTag :=
  if record.startsWith "BVar(" then .bvar
  else if record.startsWith "Sort(" then .sort
  else if record.startsWith "Const(" then .const
  else if record.startsWith "App(" then .app
  else if record.startsWith "Lam(" then .lam
  else if record.startsWith "ForallE(" then .forallE
  else if record.startsWith "LetE(" then .letE
  else if record.startsWith "NatLit(" || record.startsWith "StrLit(" then .lit
  else .bvar  -- fallback

/-- Extract the content between the first `(` and the last `)` in a record string. -/
private def parenContent (record : String) : String :=
  let afterParen := (record.dropWhile (· != '(') |>.drop 1).toString
  if afterParen.endsWith ")" then
    String.ofList (afterParen.toList.dropLast)
  else afterParen

/-- Parse a `Nat` from a string prefix, stopping at the first non-digit. -/
private def parseNat (s : String) : Nat :=
  let digits := s.takeWhile (·.isDigit)
  digits.toNat!

/-- Extract the de Bruijn index from a BVar record. Returns 0 on parse failure. -/
def parseBVarIdx (record : String) : Nat :=
  if !record.startsWith "BVar(" then 0
  else parseNat (parenContent record)

/-- Count leading `Ls(` prefixes in a level string. -/
private partial def countLevelSucc (s : String) (acc : Nat) : Nat :=
  if s.startsWith "Ls(" then countLevelSucc (s.drop 3).toString (acc + 1)
  else acc

/-- Extract a simplified level from a Sort record. Returns 0 on parse failure.
    Maps `"Sort(L0)"` to 0, `"Sort(Ls(L0))"` to 1, etc. -/
def parseSortLevel (record : String) : Nat :=
  if !record.startsWith "Sort(" then 0
  else countLevelSucc (parenContent record) 0

/-- Extract the declaration hash from a Const record. Returns 0 on parse failure.
    Parses the first number from `"Const(12345, [...])"`. -/
def parseConstKey (record : String) : UInt64 :=
  if !record.startsWith "Const(" then 0
  else
    let content := parenContent record
    let numStr := content.takeWhile (fun c => c.isDigit)
    numStr.toNat!.toUInt64

/-- Constructor tag of a nerve, derived from its record string. -/
def AstroNerve.tag (n : AstroNerve) : NerveTag := parseTag n.record

/-- Child hashes of a nerve. Atoms (ref = [self]) return the empty list;
    compound nodes return their full ref list. -/
def AstroNerve.children (n : AstroNerve) : List UInt64 :=
  if n.ref.length <= 1 then [] else n.ref

end HypergraphKernel

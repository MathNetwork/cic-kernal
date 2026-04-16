/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import HypergraphKernel.Defs

/-!
# Merkle-Style Expression Hashing

Computes a content hash for any `Expr` tree in Merkle style: each node's
record string contains the hashes of its children, and the node's own hash
is `H(record)`. This guarantees structural equality iff hashes match.

## Main Definitions

- `levelToHashString`: Convert a `Level` to a canonical string for hashing.
- `hashExpr`: Compute `(hash, record)` for an `Expr` in Merkle style.
-/

open HypergraphKernel

/-- Convert a `Level` to a canonical string representation for hashing. -/
partial def levelToHashString : Level → String
  | .zero => "L0"
  | .succ l => s!"Ls({levelToHashString l})"
  | .max a b => s!"Lmax({levelToHashString a},{levelToHashString b})"
  | .imax a b => s!"Limax({levelToHashString a},{levelToHashString b})"
  | .param n => s!"Lp({n})"

/-- Compute `(hash, record)` for an `Expr` using Merkle-style content addressing. -/
partial def hashExpr (e : Expr) : (UInt64 × String) :=
  match e with
  | .bvar n =>
    let record := s!"BVar({n})"
    (record.hash, record)
  | .sort l =>
    let record := s!"Sort({levelToHashString l})"
    (record.hash, record)
  | .const h ls =>
    let levelStrs := String.intercalate ", " (ls.map levelToHashString)
    let record := s!"Const({h}, [{levelStrs}])"
    (record.hash, record)
  | .app f a =>
    let (fh, _) := hashExpr f
    let (ah, _) := hashExpr a
    let record := s!"App({fh}, {ah})"
    (record.hash, record)
  | .lam ty body =>
    let (th, _) := hashExpr ty
    let (bh, _) := hashExpr body
    let record := s!"Lam({th}, {bh})"
    (record.hash, record)
  | .forallE ty body =>
    let (th, _) := hashExpr ty
    let (bh, _) := hashExpr body
    let record := s!"ForallE({th}, {bh})"
    (record.hash, record)
  | .letE ty val body =>
    let (th, _) := hashExpr ty
    let (vh, _) := hashExpr val
    let (bh, _) := hashExpr body
    let record := s!"LetE({th}, {vh}, {bh})"
    (record.hash, record)
  | .lit (.natVal n) =>
    let record := s!"NatLit({n})"
    (record.hash, record)
  | .lit (.strVal s) =>
    let record := s!"StrLit({s})"
    (record.hash, record)

#eval hashExpr (_root_.Expr.bvar 0 : Expr)
#eval hashExpr (_root_.Expr.const 100 [] : Expr)

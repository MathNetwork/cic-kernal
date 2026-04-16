/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel
import HypergraphKernel.Hash

/-!
# ExprWithHash: Expressions with Cached Content Hash

Every expression carries its content hash, computed once at construction time.
This enables O(1) equality checks via hash comparison.

## Design

- `ExprWithHash` wraps `Expr UInt64` with a cached `UInt64` hash
- Smart constructors (`mkBVar`, `mkSort`, `mkConst`, `mkApp`, ...) compute
  hash via `hashExpr` at construction time — O(n) once, then O(1) reads
- `defEqWithHash` reads `.hash` directly, never calls `hashExpr`
- Hash consistency is guaranteed: all constructors use `hashExpr`
- Future optimization: incremental `mixHash` for O(1) construction
-/

open HypergraphKernel

/-- An expression paired with its pre-computed content hash. -/
structure ExprWithHash where
  /-- The underlying CIC expression. -/
  expr : Expr UInt64
  /-- Content hash, computed once at construction time. -/
  hash : UInt64
  deriving Repr, BEq

namespace ExprWithHash

/-- Wrap a raw expression, computing its hash once. -/
def ofExpr (e : Expr UInt64) : ExprWithHash :=
  { expr := e, hash := (hashExpr e).1 }

/-- Extract the underlying expression. -/
def toExpr (e : ExprWithHash) : Expr UInt64 := e.expr

-- === Smart constructors: hash computed once via hashExpr ===

/-- BVar: hash from index. -/
def mkBVar (n : Nat) : ExprWithHash :=
  ofExpr (.bvar n)

/-- Sort: hash from level. -/
def mkSort (u : Level) : ExprWithHash :=
  ofExpr (.sort u)

/-- Const: hash from key + levels. -/
def mkConst (k : UInt64) (ls : List Level) : ExprWithHash :=
  ofExpr (.const k ls)

/-- App: hash computed from full application expression. -/
def mkApp (f a : ExprWithHash) : ExprWithHash :=
  ofExpr (.app f.expr a.expr)

/-- Lam: hash computed from full lambda expression. -/
def mkLam (ty body : ExprWithHash) : ExprWithHash :=
  ofExpr (.lam ty.expr body.expr)

/-- ForallE: hash computed from full forall expression. -/
def mkForallE (ty body : ExprWithHash) : ExprWithHash :=
  ofExpr (.forallE ty.expr body.expr)

/-- LetE: hash computed from full let expression. -/
def mkLetE (ty val body : ExprWithHash) : ExprWithHash :=
  ofExpr (.letE ty.expr val.expr body.expr)

/-- Lit: hash from literal. -/
def mkLit (l : Literal) : ExprWithHash :=
  ofExpr (.lit l)

end ExprWithHash

/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/

/-!
# Generic CIC Expression Type

Expression type parameterized on identity key `Key`.
`Key = String` gives name-based identity, `Key = UInt64` gives hash-based identity.

## Main Definitions

- `Level`: Universe level expressions with polymorphism support
- `Literal`: Numeric and string literal values
- `Expr Key`: The 8-constructor CIC expression type
-/

/-- Universe level expressions. Supports polymorphism via `param` constructor. -/
inductive Level where
  | zero : Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  | param : Nat → Level
  deriving Repr, BEq

/-- Convenience: Level 1. -/
def Level.one : Level := .succ .zero

/-- Literal values: natural numbers and strings. -/
inductive Literal where
  | natVal : Nat → Literal
  | strVal : String → Literal
  deriving Repr, BEq

/-- CIC expression type parameterized on identity key `Key`.
    8 constructors cover all kernel-level terms. -/
inductive Expr (Key : Type) where
  | bvar    : Nat → Expr Key
  | sort    : Level → Expr Key
  | const   : Key → List Level → Expr Key
  | app     : Expr Key → Expr Key → Expr Key
  | lam     : Expr Key → Expr Key → Expr Key
  | forallE : Expr Key → Expr Key → Expr Key
  | letE    : Expr Key → Expr Key → Expr Key → Expr Key
  | lit     : Literal → Expr Key
  deriving Repr, BEq

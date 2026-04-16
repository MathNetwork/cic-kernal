/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel.Expr

/-!
# Generic Declaration Types

Declaration types parameterized on `Key`, including recursor info for generic iota reduction.

## Main Definitions

- `RecRule Key`: A single recursor rule mapping a constructor key to its field count.
- `RecursorInfo Key`: Metadata for generic iota reduction (params, minors, indices, rules).
- `DeclKind Key`: Kinds of declarations, with `recursor` carrying `RecursorInfo`.
- `Decl Key`: A kernel declaration with kind, type, and optional value.
-/

/-- Recursor reduction rule: maps a constructor key to its field count. -/
structure RecRule (Key : Type) where
  constructorKey : Key
  nFields : Nat
  deriving Repr

/-- Information needed for generic iota reduction of a recursor. -/
structure RecursorInfo (Key : Type) where
  numParams : Nat
  numMinors : Nat
  numIndices : Nat := 0
  rules : List (RecRule Key)
  deriving Repr

/-- Declaration kind, parameterized on `Key` for recursor info. -/
inductive DeclKind (Key : Type) where
  | axiom
  | definition
  | constructor
  | recursor : RecursorInfo Key → DeclKind Key
  deriving Repr

/-- A kernel declaration: kind, type, optional value. -/
structure Decl (Key : Type) where
  kind : DeclKind Key
  type : Expr Key
  value : Option (Expr Key)
  deriving Repr

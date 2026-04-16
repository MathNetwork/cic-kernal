/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import Std
import GenericKernel.Decl

/-!
# Generic Environment

Maps identity keys to declarations using `HashMap`.

## Main Definitions

- `Env Key`: A generic declaration store backed by `HashMap Key (Decl Key)`.
- `Env.addDecl`: Register a new declaration under a given key.
- `Env.getDecl`: Look up a declaration by key.
-/

open Std

/-- Generic declaration store mapping `Key` to `Decl Key`. -/
structure Env (Key : Type) [BEq Key] [Hashable Key] where
  decls : HashMap Key (Decl Key) := {}

instance {Key : Type} [BEq Key] [Hashable Key] : Inhabited (Env Key) where
  default := { decls := {} }

namespace Env
variable {Key : Type} [BEq Key] [Hashable Key]

/-- Create an empty environment. -/
def empty : Env Key := { decls := {} }

/-- Look up a declaration by key. -/
def getDecl (env : Env Key) (k : Key) : Option (Decl Key) :=
  env.decls.get? k

/-- Register a declaration under the given key. -/
def addDecl (env : Env Key) (k : Key) (d : Decl Key) : Env Key :=
  { decls := env.decls.insert k d }

/-- Number of declarations. -/
def size (env : Env Key) : Nat :=
  env.decls.size

end Env

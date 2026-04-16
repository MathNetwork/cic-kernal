/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel

/-!
# HypergraphKernel: Hash-Based CIC Kernel

HypergraphKernel is `GenericKernel` instantiated with `Key = UInt64`.
All core kernel logic comes from GenericKernel; this file provides type aliases.
HypergraphKernel adds hash fast-path defEq, nerve generation.

Open `HypergraphKernel` to bring the `UInt64`-specialized aliases into scope.
-/

namespace HypergraphKernel

/-- HypergraphKernel expression type. -/
abbrev Expr := _root_.Expr UInt64

/-- HypergraphKernel declaration. -/
abbrev Decl := _root_.Decl UInt64

/-- HypergraphKernel declaration kind. -/
abbrev DeclKind := _root_.DeclKind UInt64

/-- HypergraphKernel recursor info. -/
abbrev RecursorInfo := _root_.RecursorInfo UInt64

/-- HypergraphKernel recursor rule. -/
abbrev RecRule := _root_.RecRule UInt64

-- Re-export GenericKernel namespace functions
export GenericKernel (whnf infer)

-- Re-export top-level functions
export _root_ (subst unfoldApps instantiateUnivParams)

end HypergraphKernel

/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel

/-!
# TreeKernel: Name-Based CIC Kernel

TreeKernel is `GenericKernel` instantiated with `Key = String`.
All kernel logic comes from GenericKernel; this file provides type aliases
and re-exports for convenience.

Open `TreeKernel` to bring the `String`-specialized aliases into scope.
-/

namespace TreeKernel

/-- TreeKernel expression type. -/
abbrev Expr := _root_.Expr String

/-- TreeKernel environment. -/
abbrev Env := _root_.Env String

/-- TreeKernel declaration. -/
abbrev Decl := _root_.Decl String

/-- TreeKernel declaration kind. -/
abbrev DeclKind := _root_.DeclKind String

/-- TreeKernel recursor info. -/
abbrev RecursorInfo := _root_.RecursorInfo String

/-- TreeKernel recursor rule. -/
abbrev RecRule := _root_.RecRule String

-- Re-export GenericKernel namespace functions (whnf, infer, defEq, check)
export GenericKernel (whnf infer defEq check)

-- Re-export top-level functions
export _root_ (subst unfoldApps instantiateUnivParams)

end TreeKernel

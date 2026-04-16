# Lean Style Guide (AstroCore)

## File Layout Template

```lean
/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/

import TreeKernel.Expr
import TreeKernel.Decl

/-!
# Module Title

Brief description of what this file implements.

## Main Definitions

- `foo`: one-line description
- `bar`: one-line description
-/

namespace MyNamespace

/-- Docstring for every definition. -/
def foo (x : Nat) : Nat := x + 1

end MyNamespace
```

## Naming Conventions

| Kind | Convention | Example |
|------|-----------|---------|
| Types, structures, inductives | UpperCamelCase | `Expr`, `DeclKind`, `RecursorInfo` |
| Functions, definitions | camelCase | `hashExpr`, `unfoldApps`, `whnf` |
| Theorems, lemmas | snake_case | `add_comm`, `hash_fast_path_sound` |
| Universe variables | `u`, `v`, `w` | `Sort (.param u)` |
| Type variables | Greek letters | `alpha`, `beta`, `gamma` |
| Natural number variables | `n`, `m`, `k` | `fun (n : Nat) => ...` |

## Formatting Rules

- **Line length**: 100 characters maximum.
- **Indentation**: 2 spaces for continued expressions.
- **Lambda syntax**: Use `fun` not `lambda`.
- **Pipeline**: Use `<|` not `$`.
- **Definition**: Put `:=` at end of line, not beginning of next line.
- **Types**: All argument types must be explicit. Return types must always be specified.
- **Trailing commas**: Use trailing commas in struct literals and list literals.

```lean
-- Good
def infer (env : Env) (e : Expr) (ctx : List Expr := []) : Option Expr :=
  match e with
  | .sort u => some (.sort (.succ u))
  | .bvar n => ctx.get? n
  | _ => none

-- Bad: implicit types, no return type, lambda syntax
def infer env e (ctx := []) :=
  match e with ...
```

## Docstring Requirements

Every `def`, `structure`, and `inductive` must have a `/-- -/` docstring above it:

```lean
/-- Substitute `arg` for `BVar(0)` in `e`, decrementing higher BVar indices.
    `depth` tracks how many binders we've descended through. -/
partial def subst (e : Expr) (arg : Expr) (depth : Nat := 0) : Expr :=
  ...
```

Every file must have a `/-! -/` module docstring after the imports.

Use `--` for inline comments explaining non-obvious logic (especially BVar indices).

## Function Length

- No function should exceed 40 lines.
- If a function is too long, extract helper functions.
- Each `match` arm should be understandable in isolation.
- Name intermediate values rather than deeply nesting expressions.

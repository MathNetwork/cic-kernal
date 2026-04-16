/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import TreeKernel

/-!
# Nat.add Verification Demo (Name-Based)

End-to-end demonstration of the name-based TreeKernel. Registers `Nat`,
`Nat.zero`, `Nat.succ`, and `Nat.rec`, then type-checks `Nat.add` and
prints the environment as JSON.

## Main Definitions

- `natType`: The type of `Nat`, i.e. `Sort(1)`.
- `addValue`: The definition body of `Nat.add` using `Nat.rec`.
- `main`: IO entry point that builds the environment step-by-step.
-/

open TreeKernel

/-- The type of `Nat`: `Sort(1)`. -/
def natType : Expr := .sort Level.one

/-- The type of `Nat.zero`: `Nat`. -/
def zeroType : Expr := .const "Nat" []

/-- The type of `Nat.succ`: `Nat -> Nat`. -/
def succType : Expr := .forallE (.const "Nat" []) (.const "Nat" [])

/-- The type of `Nat.rec` (simplified for Nat.add). -/
def recType : Expr :=
  .forallE
    (.forallE (.const "Nat" []) (.sort (.param 0)))
    (.forallE
      (.const "Nat" [])
      (.forallE
        (.forallE (.const "Nat" []) (.forallE (.const "Nat" []) (.const "Nat" [])))
        (.forallE
          (.const "Nat" [])
          (.const "Nat" []))))

/-- RecursorInfo for Nat.rec: 1 param (motive), 2 minors (base, step), rules for zero and succ. -/
def natRecInfo : RecursorInfo := {
  numParams := 1,
  numMinors := 2,
  rules := [
    { constructorKey := "Nat.zero", nFields := 0 },
    { constructorKey := "Nat.succ", nFields := 1 },
  ]
}

/-- The type of `Nat.add`: `Nat -> Nat -> Nat`. -/
def addType : Expr := .forallE (.const "Nat" []) (.forallE (.const "Nat" []) (.const "Nat" []))

/-- The definition body of `Nat.add`: `fun m n => Nat.rec (fun _ => Nat) m (fun k ih => succ ih) n`. -/
def addValue : Expr :=
  .lam (.const "Nat" [])                              -- fun (m : Nat) =>
    (.lam (.const "Nat" [])                            --   fun (n : Nat) =>
      (.app                                            --     App(
        (.app                                          --       App(
          (.app                                        --         App(
            (.app                                      --           App(
              (.const "Nat.rec" [Level.one])            --             Nat.rec @{1},
              (.lam (.const "Nat" []) (.const "Nat" []))) --           motive: fun _ => Nat),
            (.bvar 1))                                 --           m),
          (.lam (.const "Nat" [])                      --         fun (k : Nat) =>
            (.lam (.const "Nat" [])                    --           fun (ih : Nat) =>
              (.app (.const "Nat.succ" []) (.bvar 0)))))--          succ(ih)),
        (.bvar 0)))                                    --       n)

/-- Build environment, type-check `Nat.add`, and print JSON. -/
def main : IO Unit := do
  -- start from an empty Env
  let mut env := Env.empty

  -- Step 1: register Nat : Sort(1)
  match check "Nat" natType none .constructor env with
  | some env' =>
      env := env'
      IO.println "✓ Nat : Sort(1)"
  | none => IO.println "✗ Nat failed"

  -- Step 2: register Nat.zero : Nat
  match check "Nat.zero" zeroType none .constructor env with
  | some env' =>
      env := env'
      IO.println "✓ Nat.zero : Nat"
  | none => IO.println "✗ Nat.zero failed"

  -- Step 3: register Nat.succ : Nat -> Nat
  match check "Nat.succ" succType none .constructor env with
  | some env' =>
      env := env'
      IO.println "✓ Nat.succ : Nat → Nat"
  | none => IO.println "✗ Nat.succ failed"

  -- Step 4: register Nat.rec
  match check "Nat.rec" recType none (.recursor natRecInfo) env with
  | some env' =>
      env := env'
      IO.println "✓ Nat.rec"
  | none => IO.println "✗ Nat.rec failed"

  -- Step 5: check and register Nat.add : Nat -> Nat -> Nat
  match check "Nat.add" addType (some addValue) .definition env with
  | some env' =>
      env := env'
      IO.println "✓ Nat.add : Nat → Nat → Nat"
  | none => IO.println "✗ Nat.add failed — infer(v) ≠ T"

  IO.println ""
  IO.println s!"Env size: {env.size} declarations"
  IO.println ""
  IO.println "=== JSON ==="
  IO.println (env.toJson)

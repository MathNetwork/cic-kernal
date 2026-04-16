/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import TreeKernel

open TreeKernel

/-!
# TreeKernel Shared Setup

Shared declarations, registration chain, and helper functions for all TreeKernel examples.
Provides `env8` (environment with Nat + Eq infrastructure) and all proof helper functions.
-/

deriving instance Inhabited for TreeKernel.Env

-- === Nat declarations ===
def natType : Expr := .sort Level.one
def zeroType : Expr := .const "Nat" []
def succType : Expr := .forallE (.const "Nat" []) (.const "Nat" [])
def recType : Expr :=
  .forallE (.forallE (.const "Nat" []) (.sort (.param 0)))
    (.forallE (.const "Nat" [])
      (.forallE (.forallE (.const "Nat" []) (.forallE (.const "Nat" []) (.const "Nat" [])))
        (.forallE (.const "Nat" []) (.const "Nat" []))))
def addType : Expr := .forallE (.const "Nat" []) (.forallE (.const "Nat" []) (.const "Nat" []))
def addValue : Expr :=
  .lam (.const "Nat" [])
    (.lam (.const "Nat" [])
      (.app (.app (.app (.app (.const "Nat.rec" [Level.one])
        (.lam (.const "Nat" []) (.const "Nat" [])))
        (.bvar 1))
        (.lam (.const "Nat" []) (.lam (.const "Nat" []) (.app (.const "Nat.succ" []) (.bvar 0)))))
        (.bvar 0)))

-- Nat.rec PROPER dependent type:
-- ∀ (motive : Nat → Sort u), motive zero → (∀ n, motive n → motive (succ n)) → ∀ n, motive n
def recType2 : Expr :=
  .forallE (.forallE (.const "Nat" []) (.sort (.param 0)))              -- motive : Nat → Sort u
    (.forallE (.app (.bvar 0) (.const "Nat.zero" []))           -- base : motive zero
      (.forallE                                              -- step : ∀ n, motive n → motive (succ n)
        (.forallE (.const "Nat" [])                             --   n : Nat
          (.forallE (.app (.bvar 2) (.bvar 0))               --   ih : motive n
            (.app (.bvar 3) (.app (.const "Nat.succ" []) (.bvar 1)))))  --   motive (succ n)
        (.forallE (.const "Nat" [])                             -- n : Nat
          (.app (.bvar 3) (.bvar 0)))))                      -- motive n

def natRecInfo : RecursorInfo := {
  numParams := 1,
  numMinors := 2,
  rules := [
    { constructorKey := "Nat.zero", nFields := 0 },
    { constructorKey := "Nat.succ", nFields := 1 },
  ]
}

-- === Registration chain ===
def env0 : TreeKernel.Env := _root_.Env.empty
def env1 := (check "Nat" natType none .constructor env0).get!
def env2 := (check "Nat.zero" zeroType none .constructor env1).get!
def env3 := (check "Nat.succ" succType none .constructor env2).get!
def env4 := (check "Nat.rec" recType2 none (.recursor natRecInfo) env3).get!
def env5 := (check "Nat.add" addType (some addValue) .definition env4).get!

-- === Eq declarations ===

-- Eq : ∀ (α : Sort 1), α → α → Sort 0
def eqType : Expr :=
  .forallE (.sort Level.one)
    (.forallE (.bvar 0)
      (.forallE (.bvar 1)
        (.sort .zero)))

def env6 := (check "Eq" eqType none .axiom env5).get!

-- Eq.refl : ∀ (α : Sort 1) (a : α), Eq α a a
def eqReflType : Expr :=
  .forallE (.sort Level.one)
    (.forallE (.bvar 0)
      (.app (.app (.app (.const "Eq" []) (.bvar 1)) (.bvar 0)) (.bvar 0)))

def env7 := (check "Eq.refl" eqReflType none .constructor env6).get!

-- Eq.rec : ∀ (α : Sort 1) (a : α) (motive : α → Sort 1) (refl_case : motive a) (b : α)
--            (h : Eq α a b), motive b
def eqRecType : Expr :=
  .forallE (.sort Level.one)                                    -- α : Type
    (.forallE (.bvar 0)                                 -- a : α
      (.forallE (.forallE (.bvar 1) (.sort Level.one))          -- motive : α → Type
        (.forallE (.app (.bvar 0) (.bvar 1))            -- refl_case : motive a
          (.forallE (.bvar 3)                           -- b : α
            (.forallE                                   -- h : Eq α a b
              (.app (.app (.app (.const "Eq" []) (.bvar 4)) (.bvar 3)) (.bvar 0))
              (.app (.bvar 3) (.bvar 1)))))))            -- motive b

def eqRecInfo : RecursorInfo := {
  numParams := 3,       -- α, a, motive
  numMinors := 1,       -- refl_case
  numIndices := 1,      -- b
  rules := [
    { constructorKey := "Eq.refl", nFields := 0 },
  ]
}

def env8 := (check "Eq.rec" eqRecType none (.recursor eqRecInfo) env7).get!

-- === Helper functions ===
def mkAdd (a b : Expr) : Expr := .app (.app (.const "Nat.add" []) a) b
def mkSucc (n : Expr) : Expr := .app (.const "Nat.succ" []) n
def mkEq (a b : Expr) : Expr := .app (.app (.app (.const "Eq" []) (.const "Nat" [])) a) b
def mkRefl (a : Expr) : Expr := .app (.app (.const "Eq.refl" []) (.const "Nat" [])) a
def mkEqRec (a motive reflCase b h : Expr) : Expr :=
  .app (.app (.app (.app (.app (.app (.const "Eq.rec" []) (.const "Nat" [])) a) motive) reflCase) b) h

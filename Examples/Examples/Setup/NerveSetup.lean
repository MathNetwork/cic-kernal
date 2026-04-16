/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import HypergraphKernel

open HypergraphKernel

/-!
# HypergraphKernel Shared Setup

Shared declarations, registration chain, and helper functions for all HypergraphKernel examples.
Provides `net8` (network with Nat + Eq infrastructure) and all proof helper functions.
-/

deriving instance Inhabited for AstroNet

-- === Nat declarations ===
def natType : Expr := .sort Level.one
def hNat : UInt64 := (hashExpr natType).1
def zeroType : Expr := .const hNat []
def hZero : UInt64 := (hashExpr zeroType).1
def succType : Expr := .forallE (.const hNat []) (.const hNat [])
def hSucc : UInt64 := (hashExpr succType).1
-- Nat.rec (universe-polymorphic, motive → Sort (.param 0))
def recType : Expr :=
  .forallE (.forallE (.const hNat []) (.sort (.param 0)))
    (.forallE (.app (.bvar 0) (.const hZero []))
      (.forallE
        (.forallE (.const hNat [])
          (.forallE (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const hSucc []) (.bvar 1)))))
        (.forallE (.const hNat [])
          (.app (.bvar 3) (.bvar 0)))))
def hRec : UInt64 := (hashExpr recType).1
def addType : Expr := .forallE (.const hNat []) (.forallE (.const hNat []) (.const hNat []))
def hNatAdd : UInt64 := (hashExpr addType).1
def addValue : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.app (.app (.app (.app (.const hRec [Level.one])
        (.lam (.const hNat []) (.const hNat [])))
        (.bvar 1))
        (.lam (.const hNat []) (.lam (.const hNat []) (.app (.const hSucc []) (.bvar 0)))))
        (.bvar 0)))

def natRecInfo : RecursorInfo := {
  numParams := 1,
  numMinors := 2,
  rules := [
    { constructorKey := hZero, nFields := 0 },
    { constructorKey := hSucc, nFields := 1 },
  ]
}

-- === Registration chain ===
def env0 : Env UInt64 := Env.empty
def env1 := (check hNat natType none .constructor env0).get!
def env2 := (check hZero zeroType none .constructor env1).get!
def env3 := (check hSucc succType none .constructor env2).get!
def env4 := (check hRec recType none (.recursor natRecInfo) env3).get!
def env5 := (check hNatAdd addType (some addValue) .definition env4).get!

-- === Eq declarations ===

-- Eq : ∀ (α : Sort 1), α → α → Sort 0
def eqType : Expr :=
  .forallE (.sort Level.one)
    (.forallE (.bvar 0)
      (.forallE (.bvar 1)
        (.sort .zero)))
def hEq : UInt64 := (hashExpr eqType).1

def env6 := (check hEq eqType none .axiom env5).get!

-- Eq.refl : ∀ (α : Sort 1) (a : α), Eq α a a
def eqReflType : Expr :=
  .forallE (.sort Level.one)
    (.forallE (.bvar 0)
      (.app (.app (.app (.const hEq []) (.bvar 1)) (.bvar 0)) (.bvar 0)))
def hEqRefl : UInt64 := (hashExpr eqReflType).1

def env7 := (check hEqRefl eqReflType none .constructor env6).get!

-- Eq.rec : ∀ (α : Sort 1) (a : α) (motive : α → Sort 1) (refl_case : motive a) (b : α)
--            (h : Eq α a b), motive b
def eqRecType : Expr :=
  .forallE (.sort Level.one)                                    -- α : Type
    (.forallE (.bvar 0)                                 -- a : α
      (.forallE (.forallE (.bvar 1) (.sort Level.one))          -- motive : α → Type
        (.forallE (.app (.bvar 0) (.bvar 1))            -- refl_case : motive a
          (.forallE (.bvar 3)                           -- b : α
            (.forallE                                   -- h : Eq α a b
              (.app (.app (.app (.const hEq []) (.bvar 4)) (.bvar 3)) (.bvar 0))
              (.app (.bvar 3) (.bvar 1)))))))            -- motive b
def hEqRec : UInt64 := (hashExpr eqRecType).1

def eqRecInfo : RecursorInfo := {
  numParams := 3,       -- α, a, motive
  numMinors := 1,       -- refl_case
  numIndices := 1,      -- b
  rules := [
    { constructorKey := hEqRefl, nFields := 0 },
  ]
}

def env8 := (check hEqRec eqRecType none (.recursor eqRecInfo) env7).get!

-- === Helper functions ===
def mkAdd (a b : Expr) : Expr := .app (.app (.const hNatAdd []) a) b
def mkSucc' (n : Expr) : Expr := .app (.const hSucc []) n
def mkEq (a b : Expr) : Expr := .app (.app (.app (.const hEq []) (.const hNat [])) a) b
def mkRefl (a : Expr) : Expr := .app (.app (.const hEqRefl []) (.const hNat [])) a
def mkEqRec (a motive reflCase b h : Expr) : Expr :=
  .app (.app (.app (.app (.app (.app (.const hEqRec []) (.const hNat [])) a) motive) reflCase) b) h

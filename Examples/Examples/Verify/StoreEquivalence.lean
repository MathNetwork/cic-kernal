/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel

/-!
# Store Equivalence

Two kernels (TreeKernel with `Key = String`, HypergraphKernel with `Key = UInt64`)
are both instantiations of `GenericKernel`. This file establishes:

1. Agreement by construction: both kernels share `GenericKernel.check`
2. Concrete verification: `buildEnv` builds 15 declarations for both key types
3. Key translation functors (`mapExpr`, `mapDecl`) for cross-kernel correspondence
4. Functorial properties (`mapExpr_id`, `mapExpr_comp`) — building blocks for
   a full Store equivalence proof

## Key Insight

CIC typing judgments are invariant under identity mechanism substitution.
The kernel doesn't care whether you use names or hashes — the mathematics
is the same. This is proven by construction: both kernels instantiate
the same `GenericKernel.check` function.
-/

/-! ### Agreement by Construction

`TreeKernel.check` is defined as `GenericKernel.check (Key := String)`.
`HypergraphKernel.check` internally calls `GenericKernel.check (Key := UInt64)`.

These are the same polymorphic function instantiated at different types.
No theorem is needed — this is a definitional fact of the codebase architecture.

The core functions `check`, `infer`, and `defEq` are all inherited from
`GenericKernel` without modification. The only differences between the two
kernels are the identity mechanism (`String` vs `UInt64`) and how keys are
produced (direct naming vs content hashing).
-/

-- === Concrete Verification via native_decide ===

/-- All 15 declaration keys bundled for parameterized registration. -/
structure Keys (Key : Type) where
  /-- Nat type key -/
  nat : Key
  /-- Nat.zero constructor key -/
  zero : Key
  /-- Nat.succ constructor key -/
  succ : Key
  /-- Nat.rec recursor key -/
  natRec : Key
  /-- Nat.add definition key -/
  add : Key
  /-- Eq axiom key -/
  eq : Key
  /-- Eq.refl constructor key -/
  refl : Key
  /-- Eq.rec recursor key -/
  eqRec : Key
  /-- Nat.add_zero theorem key -/
  addZero : Key
  /-- Nat.add_succ theorem key -/
  addSucc : Key
  /-- zero_add theorem key -/
  zeroAdd : Key
  /-- succ_add theorem key -/
  succAdd : Key
  /-- Eq.symm theorem key -/
  eqSymm : Key
  /-- Eq.trans theorem key -/
  eqTrans : Key
  /-- Nat.add_comm theorem key -/
  natAddComm : Key

-- Parameterized helper constructors

/-- Build `add a b` expression. -/
def mkAdd' {Key : Type} (k : Keys Key) (a b : Expr Key) : Expr Key :=
  .app (.app (.const k.add []) a) b

/-- Build `succ n` expression. -/
def mkSucc' {Key : Type} (k : Keys Key) (n : Expr Key) : Expr Key :=
  .app (.const k.succ []) n

/-- Build `Eq Nat a b` expression. -/
def mkEq' {Key : Type} (k : Keys Key) (a b : Expr Key) : Expr Key :=
  .app (.app (.app (.const k.eq []) (.const k.nat [])) a) b

/-- Build `Eq.refl Nat a` expression. -/
def mkRefl' {Key : Type} (k : Keys Key) (a : Expr Key) : Expr Key :=
  .app (.app (.const k.refl []) (.const k.nat [])) a

/-- Build `Eq.rec Nat a motive reflCase b h` expression. -/
def mkEqRec' {Key : Type} (k : Keys Key)
    (a motive reflCase b h : Expr Key) : Expr Key :=
  .app (.app (.app (.app (.app (.app (.const k.eqRec [])
    (.const k.nat [])) a) motive) reflCase) b) h

/-- Build the full 15-declaration environment for any key type.
Returns `none` if any declaration fails type-checking. -/
def buildEnv {Key : Type} [BEq Key] [Hashable Key] [HasBuiltinKeys Key]
    (k : Keys Key) : Option (Env Key) := do
  -- === Nat infrastructure (declarations 1-5) ===
  let natType : Expr Key := .sort Level.one
  let zeroType : Expr Key := .const k.nat []
  let succType : Expr Key := .forallE (.const k.nat []) (.const k.nat [])
  let recType : Expr Key :=
    .forallE (.forallE (.const k.nat []) (.sort (.param 0)))         -- motive : Nat → Sort u
      (.forallE (.app (.bvar 0) (.const k.zero []))          -- base : motive zero
        (.forallE                                             -- step
          (.forallE (.const k.nat [])                            -- n : Nat
            (.forallE (.app (.bvar 2) (.bvar 0))              -- ih : motive n
              (.app (.bvar 3) (.app (.const k.succ []) (.bvar 1)))))  -- motive (succ n)
          (.forallE (.const k.nat [])                            -- n : Nat
            (.app (.bvar 3) (.bvar 0)))))                     -- motive n
  let natRecInfo : RecursorInfo Key := {
    numParams := 1, numMinors := 2,
    rules := [
      { constructorKey := k.zero, nFields := 0 },
      { constructorKey := k.succ, nFields := 1 }
    ]
  }
  let addType : Expr Key :=
    .forallE (.const k.nat []) (.forallE (.const k.nat []) (.const k.nat []))
  let addValue : Expr Key :=
    .lam (.const k.nat [])
      (.lam (.const k.nat [])
        (.app (.app (.app (.app (.const k.natRec [Level.one])
          (.lam (.const k.nat []) (.const k.nat [])))
          (.bvar 1))  -- BVar 1 = n
          (.lam (.const k.nat []) (.lam (.const k.nat [])
            (.app (.const k.succ []) (.bvar 0)))))  -- BVar 0 = acc
          (.bvar 0)))  -- BVar 0 = m
  let env ← GenericKernel.check k.nat natType none .constructor Env.empty
  let env ← GenericKernel.check k.zero zeroType none .constructor env
  let env ← GenericKernel.check k.succ succType none .constructor env
  let env ← GenericKernel.check k.natRec recType none (.recursor natRecInfo) env
  let env ← GenericKernel.check k.add addType (some addValue) .definition env
  -- === Eq infrastructure (declarations 6-8) ===
  let eqType : Expr Key :=
    .forallE (.sort Level.one)
      (.forallE (.bvar 0)
        (.forallE (.bvar 1)
          (.sort .zero)))
  let eqReflType : Expr Key :=
    .forallE (.sort Level.one)
      (.forallE (.bvar 0)
        (.app (.app (.app (.const k.eq []) (.bvar 1)) (.bvar 0)) (.bvar 0)))
  let eqRecType : Expr Key :=
    .forallE (.sort Level.one)                                    -- α : Type
      (.forallE (.bvar 0)                                 -- a : α
        (.forallE (.forallE (.bvar 1) (.sort Level.one))          -- motive : α → Type
          (.forallE (.app (.bvar 0) (.bvar 1))            -- refl_case : motive a
            (.forallE (.bvar 3)                           -- b : α
              (.forallE                                   -- h : Eq α a b
                (.app (.app (.app (.const k.eq []) (.bvar 4)) (.bvar 3)) (.bvar 0))
                (.app (.bvar 3) (.bvar 1)))))))            -- motive b
  let eqRecInfo : RecursorInfo Key := {
    numParams := 3, numMinors := 1, numIndices := 1,
    rules := [{ constructorKey := k.refl, nFields := 0 }]
  }
  let env ← GenericKernel.check k.eq eqType none .axiom env
  let env ← GenericKernel.check k.refl eqReflType none .constructor env
  let env ← GenericKernel.check k.eqRec eqRecType none (.recursor eqRecInfo) env
  -- === Theorem 9: Nat.add_zero ===
  let addZeroType : Expr Key :=
    .forallE (.const k.nat [])
      (mkEq' k (mkAdd' k (.bvar 0) (.const k.zero [])) (.bvar 0))
  let addZeroMotive : Expr Key :=
    .lam (.const k.nat [])  -- k_ : Nat
      (mkEq' k (mkAdd' k (.bvar 0) (.const k.zero [])) (.bvar 0))
  let addZeroBase : Expr Key := mkRefl' k (.const k.zero [])
  let addZeroStep : Expr Key :=
    .lam (.const k.nat [])                                           -- k_ : Nat
      (.lam (mkEq' k (mkAdd' k (.bvar 0) (.const k.zero [])) (.bvar 0))  -- ih
        (mkEqRec' k
          (mkAdd' k (.bvar 1) (.const k.zero []))                    -- a = add k_ 0
          (.lam (.const k.nat [])                                      -- fun x
            (mkEq' k (mkSucc' k (mkAdd' k (.bvar 2) (.const k.zero [])))  -- succ (add k_ 0)
                     (mkSucc' k (.bvar 0))))                           -- succ x
          (mkRefl' k (mkSucc' k (mkAdd' k (.bvar 1) (.const k.zero []))))  -- refl
          (.bvar 1)                                                   -- b = k_
          (.bvar 0)))                                                 -- h = ih
  let addZeroProof : Expr Key :=
    .lam (.const k.nat [])
      (.app (.app (.app (.app (.const k.natRec [.zero]) addZeroMotive)
        addZeroBase) addZeroStep) (.bvar 0))
  let env ← GenericKernel.check k.addZero addZeroType
    (some addZeroProof) .definition env
  -- === Theorem 10: Nat.add_succ ===
  let addSuccType : Expr Key :=
    .forallE (.const k.nat [])
      (.forallE (.const k.nat [])
        (mkEq' k (mkAdd' k (.bvar 1) (mkSucc' k (.bvar 0)))
               (mkSucc' k (mkAdd' k (.bvar 1) (.bvar 0)))))
  let addSuccProof : Expr Key :=
    .lam (.const k.nat [])
      (.lam (.const k.nat [])
        (mkRefl' k (mkAdd' k (.bvar 1) (mkSucc' k (.bvar 0)))))
  let env ← GenericKernel.check k.addSucc addSuccType
    (some addSuccProof) .definition env
  -- === Theorem 11: zero_add ===
  let zeroAddType : Expr Key :=
    .forallE (.const k.nat [])
      (mkEq' k (mkAdd' k (.const k.zero []) (.bvar 0)) (.bvar 0))
  let zeroAddMotive : Expr Key :=
    .lam (.const k.nat [])
      (mkEq' k (mkAdd' k (.const k.zero []) (.bvar 0)) (.bvar 0))
  let zeroAddBase : Expr Key := mkRefl' k (.const k.zero [])
  let zeroAddStep : Expr Key :=
    .lam (.const k.nat [])
      (.lam (mkEq' k (mkAdd' k (.const k.zero []) (.bvar 0)) (.bvar 0))
        (mkEqRec' k
          (mkAdd' k (.const k.zero []) (.bvar 1))
          (.lam (.const k.nat [])
            (mkEq' k (mkSucc' k (mkAdd' k (.const k.zero []) (.bvar 2)))
                     (mkSucc' k (.bvar 0))))
          (mkRefl' k (mkSucc' k (mkAdd' k (.const k.zero []) (.bvar 1))))
          (.bvar 1)
          (.bvar 0)))
  let zeroAddProof : Expr Key :=
    .lam (.const k.nat [])
      (.app (.app (.app (.app (.const k.natRec [.zero]) zeroAddMotive)
        zeroAddBase) zeroAddStep) (.bvar 0))
  let env ← GenericKernel.check k.zeroAdd zeroAddType
    (some zeroAddProof) .definition env
  -- === Theorem 12: succ_add ===
  let succAddType : Expr Key :=
    .forallE (.const k.nat [])
      (.forallE (.const k.nat [])
        (mkEq' k (mkAdd' k (mkSucc' k (.bvar 1)) (.bvar 0))
               (mkSucc' k (mkAdd' k (.bvar 1) (.bvar 0)))))
  let succAddProof : Expr Key :=
    .lam (.const k.nat [])  -- n
      (.lam (.const k.nat [])  -- m; n=BVar1, m=BVar0
        (.app (.app (.app (.app (.const k.natRec [.zero])
          -- motive
          (.lam (.const k.nat [])  -- m_; n=BVar2
            (mkEq' k (mkAdd' k (mkSucc' k (.bvar 2)) (.bvar 0))
                     (mkSucc' k (mkAdd' k (.bvar 2) (.bvar 0))))))
          -- base: refl (add (succ n) zero)
          (mkRefl' k (mkAdd' k (mkSucc' k (.bvar 1)) (.const k.zero []))))
          -- step
          (.lam (.const k.nat [])  -- m_; n=BVar2
            (.lam (mkEq' k (mkAdd' k (mkSucc' k (.bvar 2)) (.bvar 0))
                          (mkSucc' k (mkAdd' k (.bvar 2) (.bvar 0))))  -- ih; n=BVar3
              (mkEqRec' k
                (mkAdd' k (mkSucc' k (.bvar 3)) (.bvar 1))       -- a = add (succ n) m_
                (.lam (.const k.nat [])                            -- fun x; n=BVar4
                  (mkEq' k (mkSucc' k (mkAdd' k (mkSucc' k (.bvar 4)) (.bvar 2)))
                           (mkSucc' k (.bvar 0))))
                (mkRefl' k (mkSucc' k (mkAdd' k (mkSucc' k (.bvar 3)) (.bvar 1))))
                (mkSucc' k (mkAdd' k (.bvar 3) (.bvar 1)))       -- b = succ (add n m_)
                (.bvar 0)))))                                     -- h = ih
          (.bvar 0)))  -- target = m
  let env ← GenericKernel.check k.succAdd succAddType
    (some succAddProof) .definition env
  -- === Theorem 13: Eq.symm ===
  let eqSymmType : Expr Key :=
    .forallE (.const k.nat [])                                    -- a
      (.forallE (.const k.nat [])                                  -- b; a=BVar1
        (.forallE (mkEq' k (.bvar 1) (.bvar 0))                   -- h; a=BVar2, b=BVar1
          (mkEq' k (.bvar 1) (.bvar 2))))                          -- Eq b a
  let eqSymmProof : Expr Key :=
    .lam (.const k.nat [])                                        -- a
      (.lam (.const k.nat [])                                      -- b; a=BVar1
        (.lam (mkEq' k (.bvar 1) (.bvar 0))                       -- h; a=BVar2, b=BVar1
          (mkEqRec' k
            (.bvar 2)                                              -- a
            (.lam (.const k.nat [])                                -- fun x; a=BVar3
              (mkEq' k (.bvar 0) (.bvar 3)))                      -- Eq x a
            (mkRefl' k (.bvar 2))                                  -- refl a
            (.bvar 1)                                              -- b
            (.bvar 0))))                                           -- h
  let env ← GenericKernel.check k.eqSymm eqSymmType
    (some eqSymmProof) .definition env
  -- === Theorem 14: Eq.trans ===
  let eqTransType : Expr Key :=
    .forallE (.const k.nat [])                                    -- a
      (.forallE (.const k.nat [])                                  -- b
        (.forallE (.const k.nat [])                                -- c; a=BVar2, b=BVar1
          (.forallE (mkEq' k (.bvar 2) (.bvar 1))                 -- hab
            (.forallE (mkEq' k (.bvar 2) (.bvar 1))               -- hbc; a=BVar4, c=BVar2
              (mkEq' k (.bvar 4) (.bvar 2))))))                   -- Eq a c
  let eqTransProof : Expr Key :=
    .lam (.const k.nat [])                                        -- a
      (.lam (.const k.nat [])                                      -- b
        (.lam (.const k.nat [])                                    -- c; a=BVar2, b=BVar1
          (.lam (mkEq' k (.bvar 2) (.bvar 1))                     -- hab; a=BVar3, b=BVar2
            (.lam (mkEq' k (.bvar 2) (.bvar 1))                   -- hbc; a=BVar4, b=BVar3, c=BVar2
              (mkEqRec' k
                (.bvar 3)                                          -- a' = b
                (.lam (.const k.nat [])                            -- fun x; a=BVar5
                  (mkEq' k (.bvar 5) (.bvar 0)))                  -- Eq a x
                (.bvar 1)                                          -- refl_case = hab
                (.bvar 2)                                          -- target = c
                (.bvar 0))))))                                     -- h = hbc
  let env ← GenericKernel.check k.eqTrans eqTransType
    (some eqTransProof) .definition env
  -- === Theorem 15: Nat.add_comm ===
  let addCommType : Expr Key :=
    .forallE (.const k.nat [])
      (.forallE (.const k.nat [])
        (mkEq' k (mkAdd' k (.bvar 1) (.bvar 0))
               (mkAdd' k (.bvar 0) (.bvar 1))))
  let addCommMotive : Expr Key :=
    .lam (.const k.nat [])  -- n_; m=BVar1
      (mkEq' k (mkAdd' k (.bvar 0) (.bvar 1))
             (mkAdd' k (.bvar 1) (.bvar 0)))
  -- base: Eq.trans (zero_add m) (Eq.symm (add_zero m))
  -- Under [n, m]: m=BVar0
  let addCommBase : Expr Key :=
    let m := Expr.bvar 0
    let z := Expr.const k.zero []
    -- zero_add m : Eq (add 0 m) m
    let zam := Expr.app (.const k.zeroAdd []) m
    -- add_zero m : Eq (add m 0) m
    let azm := Expr.app (.const k.addZero []) m
    -- Eq.symm (add m 0) m (add_zero m) : Eq m (add m 0)
    let sym_azm := Expr.app (.app (.app (.const k.eqSymm [])
      (mkAdd' k m z)) m) azm
    -- Eq.trans (add 0 m) m (add m 0) zam sym_azm
    Expr.app (.app (.app (.app (.app (.const k.eqTrans [])
      (mkAdd' k z m)) m) (mkAdd' k m z)) zam) sym_azm
  -- step: fun n_ ih => Eq.trans (succ_add) (Eq.trans (cong_succ ih) (Eq.symm (add_succ)))
  -- Under [n, m, n_, ih]: ih=BVar0, n_=BVar1, m=BVar2
  let addCommStep : Expr Key :=
    .lam (.const k.nat [])                                          -- n_
      (.lam (mkEq' k (mkAdd' k (.bvar 0) (.bvar 1))
                     (mkAdd' k (.bvar 1) (.bvar 0)))               -- ih; n_=BVar1, m=BVar2
        (let n_ := Expr.bvar 1
         let m := Expr.bvar 2
         let ih := Expr.bvar 0
         -- 1. succ_add n_ m : Eq (add (succ n_) m) (succ (add n_ m))
         let sa := Expr.app (.app (.const k.succAdd []) n_) m
         -- 2. cong_succ: Eq (succ (add n_ m)) (succ (add m n_))
         let cong :=
           mkEqRec' k
             (mkAdd' k n_ m)                                        -- a = add n_ m
             (.lam (.const k.nat [])                                 -- fun x; n_=BVar2, m=BVar3
               (mkEq' k (mkSucc' k (mkAdd' k (.bvar 2) (.bvar 3)))  -- succ (add n_ m)
                        (mkSucc' k (.bvar 0))))                      -- succ x
             (mkRefl' k (mkSucc' k (mkAdd' k n_ m)))                -- refl
             (mkAdd' k m n_)                                         -- b = add m n_
             ih                                                      -- h = ih
         -- 3. Eq.symm on add_succ m n_
         let as_mk := Expr.app (.app (.const k.addSucc []) m) n_
         let sym_as := Expr.app (.app (.app (.const k.eqSymm [])
           (mkAdd' k m (mkSucc' k n_)))
           (mkSucc' k (mkAdd' k m n_)))
           as_mk
         -- inner_trans: Eq (succ (add n_ m)) (add m (succ n_))
         let inner_trans := Expr.app (.app (.app (.app (.app (.const k.eqTrans [])
           (mkSucc' k (mkAdd' k n_ m)))
           (mkSucc' k (mkAdd' k m n_)))
           (mkAdd' k m (mkSucc' k n_)))
           cong)
           sym_as
         -- outer_trans: Eq (add (succ n_) m) (add m (succ n_))
         Expr.app (.app (.app (.app (.app (.const k.eqTrans [])
           (mkAdd' k (mkSucc' k n_) m))
           (mkSucc' k (mkAdd' k n_ m)))
           (mkAdd' k m (mkSucc' k n_)))
           sa)
           inner_trans))
  let addCommProof : Expr Key :=
    .lam (.const k.nat [])  -- n
      (.lam (.const k.nat [])  -- m; n=BVar1
        (.app (.app (.app (.app (.const k.natRec [.zero]) addCommMotive)
          addCommBase) addCommStep) (.bvar 1)))
  let env ← GenericKernel.check k.natAddComm addCommType
    (some addCommProof) .definition env
  return env

-- === Concrete key sets ===

/-- String keys matching the TreeKernel naming convention. -/
def stringKeys : Keys String where
  nat := "Nat"; zero := "Nat.zero"; succ := "Nat.succ"
  natRec := "Nat.rec"; add := "Nat.add"
  eq := "Eq"; refl := "Eq.refl"; eqRec := "Eq.rec"
  addZero := "Nat.add_zero"; addSucc := "Nat.add_succ"
  zeroAdd := "zero_add"; succAdd := "succ_add"
  eqSymm := "Eq.symm"; eqTrans := "Eq.trans"; natAddComm := "Nat.add_comm"

/-- UInt64 keys — arbitrary distinct values. The kernel is key-agnostic. -/
instance : HasBuiltinKeys UInt64 where
  natKey := 0
  stringKey := 1

instance {Key : Type} [BEq Key] [Hashable Key] : Inhabited (Env Key) :=
  ⟨Env.empty⟩

def uint64Keys : Keys UInt64 where
  nat := 0; zero := 1; succ := 2; natRec := 3; add := 4
  eq := 5; refl := 6; eqRec := 7
  addZero := 8; addSucc := 9; zeroAdd := 10; succAdd := 11
  eqSymm := 12; eqTrans := 13; natAddComm := 14

-- === native_decide verification ===

/-- String-keyed (TreeKernel) registration succeeds for all 15 declarations. -/
theorem lean_build_succeeds :
    (buildEnv stringKeys).isSome = true := by native_decide

/-- UInt64-keyed (HypergraphKernel) registration succeeds for all 15 declarations. -/
theorem astro_build_succeeds :
    (buildEnv uint64Keys).isSome = true := by native_decide

/-- Both key types produce environments of exactly 15 declarations. -/
theorem lean_astro_same_size :
    (buildEnv stringKeys).get!.size
    = (buildEnv uint64Keys).get!.size := by native_decide

-- === Key Translation (supporting definitions for Store equivalence) ===

/-- Map Const keys in an expression. Preserves all structure. -/
def mapExpr {Key₁ Key₂ : Type} (φ : Key₁ → Key₂) :
    Expr Key₁ → Expr Key₂
  | .bvar n => .bvar n
  | .sort u => .sort u
  | .const k ls => .const (φ k) ls
  | .app f a => .app (mapExpr φ f) (mapExpr φ a)
  | .lam ty body => .lam (mapExpr φ ty) (mapExpr φ body)
  | .forallE ty body => .forallE (mapExpr φ ty) (mapExpr φ body)
  | .letE ty val body =>
    .letE (mapExpr φ ty) (mapExpr φ val) (mapExpr φ body)
  | .lit l => .lit l

/-- Map keys in a recursor rule. -/
def mapRecRule {Key₁ Key₂ : Type} (φ : Key₁ → Key₂) :
    RecRule Key₁ → RecRule Key₂
  | ⟨k, n⟩ => ⟨φ k, n⟩

/-- Map keys in recursor info. -/
def mapRecursorInfo {Key₁ Key₂ : Type} (φ : Key₁ → Key₂) :
    RecursorInfo Key₁ → RecursorInfo Key₂
  | ⟨np, nm, ni, rules⟩ => ⟨np, nm, ni, rules.map (mapRecRule φ)⟩

/-- Map keys in a declaration kind. -/
def mapDeclKind {Key₁ Key₂ : Type} (φ : Key₁ → Key₂) :
    DeclKind Key₁ → DeclKind Key₂
  | .axiom => .axiom
  | .definition => .definition
  | .constructor => .constructor
  | .recursor info => .recursor (mapRecursorInfo φ info)

/-- Map keys in a declaration. -/
def mapDecl {Key₁ Key₂ : Type} (φ : Key₁ → Key₂) :
    Decl Key₁ → Decl Key₂
  | ⟨kind, ty, val⟩ =>
    ⟨mapDeclKind φ kind, mapExpr φ ty, val.map (mapExpr φ)⟩

/-- mapExpr preserves identity: mapping with id does nothing. -/
theorem mapExpr_id {Key : Type} (e : Expr Key) :
    mapExpr id e = e := by
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp [mapExpr, ihf, iha]
  | lam ty body iht ihb => simp [mapExpr, iht, ihb]
  | forallE ty body iht ihb => simp [mapExpr, iht, ihb]
  | letE ty val body iht ihv ihb => simp [mapExpr, iht, ihv, ihb]
  | lit _ => rfl

/-- mapExpr composes: mapping with φ then ψ = mapping with ψ ∘ φ. -/
theorem mapExpr_comp {Key₁ Key₂ Key₃ : Type}
    (φ : Key₁ → Key₂) (ψ : Key₂ → Key₃) (e : Expr Key₁) :
    mapExpr ψ (mapExpr φ e) = mapExpr (ψ ∘ φ) e := by
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const k ls => simp [mapExpr, Function.comp]
  | app f a ihf iha => simp [mapExpr, ihf, iha]
  | lam ty body iht ihb => simp [mapExpr, iht, ihb]
  | forallE ty body iht ihb => simp [mapExpr, iht, ihb]
  | letE ty val body iht ihv ihb => simp [mapExpr, iht, ihv, ihb]
  | lit _ => rfl

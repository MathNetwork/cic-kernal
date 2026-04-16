/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import GenericKernel.Env

/-!
# Generic CIC Kernel

Core type-checking functions parameterized on identity key `Key`.
Iota reduction is fully generic via `RecursorInfo` — no hardcoded recursors.

## Main Definitions

- `subst`: de Bruijn substitution
- `whnf`: weak head normal form (beta, zeta, delta, generic iota)
- `infer`: type inference
- `defEq`: definitional equality (no hash fast path)
- `check`: verify and register declarations
-/

/-- Typeclass for mapping literal values to their type keys. -/
class HasBuiltinKeys (Key : Type) where
  natKey : Key
  stringKey : Key

instance : HasBuiltinKeys String where
  natKey := "Nat"
  stringKey := "String"

/-- Safe list indexing, returning `none` if index is out of bounds. -/
def listGet? (l : List α) (n : Nat) : Option α :=
  match l, n with
  | a :: _, 0 => some a
  | _ :: rest, n + 1 => listGet? rest n
  | [], _ => none

/-- Replace `Level.param n` with the n-th element of `levels`. -/
partial def Level.instantiate (l : Level) (levels : List Level) : Level :=
  match l with
  | .param n => levels.getD n .zero
  | .succ l => .succ (l.instantiate levels)
  | .max a b => .max (a.instantiate levels) (b.instantiate levels)
  | .imax a b => .imax (a.instantiate levels) (b.instantiate levels)
  | l => l

/-- Replace all `Level.param n` in an `Expr Key` with `levels[n]`. -/
partial def instantiateUnivParams {Key : Type} (e : Expr Key) (levels : List Level) : Expr Key :=
  if levels.isEmpty then e else
  match e with
  | .sort l => .sort (l.instantiate levels)
  | .const k ls => .const k (ls.map (·.instantiate levels))
  | .app f a => .app (instantiateUnivParams f levels) (instantiateUnivParams a levels)
  | .lam ty body => .lam (instantiateUnivParams ty levels) (instantiateUnivParams body levels)
  | .forallE ty body => .forallE (instantiateUnivParams ty levels) (instantiateUnivParams body levels)
  | .letE ty val body => .letE (instantiateUnivParams ty levels) (instantiateUnivParams val levels) (instantiateUnivParams body levels)
  | e => e

/-- Increment all BVar indices >= `cutoff` by `amount`. -/
partial def shift {Key : Type} (e : Expr Key) (cutoff : Nat) (amount : Nat) : Expr Key :=
  match e with
  | .bvar n => if n >= cutoff then .bvar (n + amount) else .bvar n
  | .app f a => .app (shift f cutoff amount) (shift a cutoff amount)
  | .lam ty body => .lam (shift ty cutoff amount) (shift body (cutoff + 1) amount)
  | .forallE ty body => .forallE (shift ty cutoff amount) (shift body (cutoff + 1) amount)
  | .letE ty val body => .letE (shift ty cutoff amount) (shift val cutoff amount) (shift body (cutoff + 1) amount)
  | e => e

/-- Capture-avoiding substitution. Replaces `BVar(depth)` with `arg`, adjusting indices. -/
partial def subst {Key : Type} (e : Expr Key) (arg : Expr Key) (depth : Nat := 0) : Expr Key :=
  match e with
  | .bvar n =>
      if n == depth then arg
      else if n > depth then .bvar (n - 1)
      else .bvar n
  | .app f a => .app (subst f arg depth) (subst a arg depth)
  | .lam ty body => .lam (subst ty arg depth) (subst body (shift arg 0 1) (depth + 1))
  | .forallE ty body => .forallE (subst ty arg depth) (subst body (shift arg 0 1) (depth + 1))
  | .letE ty val body => .letE (subst ty arg depth) (subst val arg depth) (subst body (shift arg 0 1) (depth + 1))
  | e => e

/-- Collect a curried application into `(head, [arg0, arg1, ...])`. -/
def unfoldApps {Key : Type} (e : Expr Key) : Expr Key × List (Expr Key) :=
  match e with
  | .app f a =>
      let (head, args) := unfoldApps f
      (head, args ++ [a])
  | e => (e, [])

/-- Find the recursor rule matching the given constructor key. -/
def findRuleIdx {Key : Type} [BEq Key] (rules : List (RecRule Key)) (ck : Key) (idx : Nat := 0) : Option (Nat × RecRule Key) :=
  match rules with
  | [] => none
  | r :: rest =>
      if r.constructorKey == ck then some (idx, r)
      else findRuleIdx rest ck (idx + 1)

/-- Apply a list of arguments to a head expression left-to-right. -/
def applyArgs {Key : Type} (head : Expr Key) (args : List (Expr Key)) : Expr Key :=
  List.foldl (fun f a => Expr.app f a) head args

namespace GenericKernel

/-- Weak head normal form reduction. Performs beta, zeta, delta, and generic iota reduction. -/
partial def whnf {Key : Type} [BEq Key] [Hashable Key] (env : Env Key) (e : Expr Key) : Expr Key :=
  match e with
  -- zeta reduction: let x := val in body -> body[val/x]
  | .letE _ty val body => whnf env (subst body val)
  -- beta reduction: (fun x => body) arg -> body[arg/x]
  | .app (.lam _ty body) arg => whnf env (subst body arg)
  -- app: iota, delta, or fn reduction
  | .app f a =>
      let whole := Expr.app f a
      let whnfApp (f' : Expr Key) : Expr Key :=
        if f' == f then whole else whnf env (Expr.app f' a)
      let fallback := fun () => whnfApp (whnf env f)
      let (head, args) := unfoldApps whole
      match head with
      | .const k levels =>
          match env.getDecl k with
          | some decl =>
              match decl.kind with
              | .recursor info =>
                  let needed := info.numParams + info.numMinors + info.numIndices + 1
                  if args.length >= needed then
                    match listGet? args (needed - 1) with
                    | none => fallback ()
                    | some target =>
                    let target' := whnf env target
                    let (tHead, tArgs) := unfoldApps target'
                    match tHead with
                    | .const ck _ =>
                        match findRuleIdx info.rules ck with
                        | some (ruleIdx, rule) =>
                            match listGet? args (info.numParams + ruleIdx) with
                            | none => fallback ()
                            | some minor =>
                            match rule.nFields with
                            | 0 => whnf env minor
                            | 1 =>
                                match listGet? tArgs 0 with
                                | none => fallback ()
                                | some n =>
                                let recArgs := args.take (info.numParams + info.numMinors)
                                let recCall := applyArgs (Expr.const k levels) (recArgs ++ [n])
                                whnf env (Expr.app (Expr.app minor n) recCall)
                            | _ =>
                                let recArgs := args.take (info.numParams + info.numMinors)
                                let withFields := tArgs.foldl (fun acc x => Expr.app acc x) minor
                                let withRecs := tArgs.foldl (fun acc x =>
                                    let rc := applyArgs (Expr.const k levels) (recArgs ++ [x])
                                    Expr.app acc rc) withFields
                                whnf env withRecs
                        | none => fallback ()
                    | _ => fallback ()
                  else fallback ()
              | _ =>
                  match decl.value with
                  | some v => whnf env (applyArgs (instantiateUnivParams v levels) args)
                  | none => fallback ()
          | none => fallback ()
      | _ => fallback ()
  -- delta reduction: standalone Const (no args)
  | .const k levels =>
      match env.getDecl k with
      | some decl =>
          match decl.value with
          | some v => whnf env (instantiateUnivParams v levels)
          | none => e
      | none => e
  -- otherwise: already in normal form
  | e => e

mutual
/-- Type inference for CIC expressions. Returns the inferred type or `none` on failure. -/
partial def infer {Key : Type} [BEq Key] [Hashable Key] [HasBuiltinKeys Key]
    (env : Env Key) (e : Expr Key) (ctx : List (Expr Key) := []) : Option (Expr Key) :=
  match e with
  | .bvar n => listGet? ctx n
  | .sort u => some (.sort (.succ u))
  | .const k levels =>
      match env.getDecl k with
      | some decl => some (instantiateUnivParams decl.type levels)
      | none => none
  | .app f a =>
      match infer env f ctx with
      | some fType =>
          let fType' := whnf env fType
          match fType' with
          | .forallE _paramType bodyType => some (whnf env (subst bodyType a))
          | _ => none
      | none => none
  | .lam ty body =>
      match infer env body (ty :: ctx) with
      | some bodyType => some (.forallE ty bodyType)
      | none => none
  | .forallE ty body =>
      match infer env ty ctx, infer env body (ty :: ctx) with
      | some tyType, some bodyType =>
          let tyType' := whnf env tyType
          let bodyType' := whnf env bodyType
          match tyType', bodyType' with
          | .sort u1, .sort u2 => some (.sort (.imax u1 u2))
          | _, _ => none
      | _, _ => none
  | .letE ty val body =>
      match infer env val ctx with
      | some valType =>
          if defEq env valType ty ctx then
            infer env (subst body val) ctx
          else none
      | none => none
  | .lit (.natVal _) => some (.const HasBuiltinKeys.natKey [])
  | .lit (.strVal _) => some (.const HasBuiltinKeys.stringKey [])

/-- Definitional equality check. Reduces both sides to WHNF then compares structurally. -/
partial def defEq {Key : Type} [BEq Key] [Hashable Key] [HasBuiltinKeys Key]
    (env : Env Key) (a b : Expr Key) (ctx : List (Expr Key) := []) : Bool :=
  let a' := whnf env a
  let b' := whnf env b
  match a', b' with
  | .sort u1, .sort u2 => u1 == u2
  | .const k1 ls1, .const k2 ls2 => k1 == k2 && ls1 == ls2
  | .bvar n1, .bvar n2 => n1 == n2
  | .app f1 a1, .app f2 a2 => defEq env f1 f2 ctx && defEq env a1 a2 ctx
  | .lam t1 b1, .lam t2 b2 => defEq env t1 t2 ctx && defEq env b1 b2 (t1 :: ctx)
  | .forallE t1 b1, .forallE t2 b2 => defEq env t1 t2 ctx && defEq env b1 b2 (t1 :: ctx)
  | .letE t1 v1 b1, .letE t2 v2 b2 =>
      defEq env t1 t2 ctx && defEq env v1 v2 ctx && defEq env b1 b2 (t1 :: ctx)
  | .lit l1, .lit l2 => l1 == l2
  | _, _ => false
end

/-- Top-level kernel entry: type-check and register a declaration in the environment. -/
def check {Key : Type} [BEq Key] [Hashable Key] [HasBuiltinKeys Key]
    (k : Key) (T : Expr Key) (v : Option (Expr Key)) (kind : DeclKind Key) (env : Env Key) : Option (Env Key) :=
  match v with
  | none =>
      let decl : Decl Key := { kind := kind, type := T, value := none }
      some (env.addDecl k decl)
  | some val =>
      match infer env val with
      | some inferredT =>
          if defEq env inferredT T then
            let decl : Decl Key := { kind := kind, type := T, value := some val }
            some (env.addDecl k decl)
          else
            none
      | none => none

end GenericKernel

# Proof Term Construction Guide

## BVar Annotation Rules

Every `.bvar N` must have a comment identifying what variable it refers to:

```lean
-- Good: clear BVar annotations
.lam (.const "Nat" [])                              -- k : Nat
  (.lam (mkEq (mkAdd (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))
                                                     -- ih : Eq Nat (add k 0) k
    (mkEqRec                                         -- k = BVar 1, ih = BVar 0
      (mkAdd (.bvar 1) (.const "Nat.zero" []))       -- a = add k 0 (BVar 1 = k)
      ...))

-- Bad: no annotations
.lam (.const "Nat" [])
  (.lam (mkEq (mkAdd (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))
    (mkEqRec (mkAdd (.bvar 1) (.const "Nat.zero" [])) ...))
```

When entering a new binder, list the full BVar assignment:
```
-- Under [n, m, k, ih]: ih=BVar0, k=BVar1, m=BVar2, n=BVar3
```

## Helper Function Catalog

### TreeKernel (name-based)

```lean
def mkAdd (a b : Expr) : Expr := .app (.app (.const "Nat.add" []) a) b
def mkSucc (n : Expr) : Expr := .app (.const "Nat.succ" []) n
def mkEq (a b : Expr) : Expr := .app (.app (.app (.const "Eq" []) (.const "Nat" [])) a) b
def mkRefl (a : Expr) : Expr := .app (.app (.const "Eq.refl" []) (.const "Nat" [])) a
def mkEqRec (a motive reflCase b h : Expr) : Expr :=
  .app (.app (.app (.app (.app (.app (.const "Eq.rec" []) (.const "Nat" [])) a) motive) reflCase) b) h
```

### HypergraphKernel (hash-based)

Same helpers but using hash constants (`hNatAdd`, `hSucc`, `hEq`, `hEqRefl`, `hEqRec`, `hNat`).
Note: HypergraphKernel uses `mkSucc'` to avoid name conflict with TreeKernel's `mkSucc`.

## Proof Patterns

### Induction (via Nat.rec)

```
fun (n : Nat) =>
  Nat.rec [universe] motive base step n
```

Where:
- `motive : Nat -> Sort u` -- what we are proving for each n
- `base : motive zero` -- proof for the base case
- `step : forall k, motive k -> motive (succ k)` -- inductive step

### Congruence (succ preserves equality)

To prove `Eq Nat (succ a) (succ b)` from `h : Eq Nat a b`:
```
Eq.rec a (fun x => Eq Nat (succ a) (succ x)) (Eq.refl Nat (succ a)) b h
```

### Transitivity

To chain `hab : Eq a b` and `hbc : Eq b c` into `Eq a c`:
```
Eq.trans a b c hab hbc
```

Or using Eq.rec directly:
```
Eq.rec b (fun x => Eq a x) hab c hbc
```

### Symmetry

To prove `Eq b a` from `h : Eq a b`:
```
Eq.rec a (fun x => Eq x a) (Eq.refl a) b h
```

## Debugging: When infer Returns none

1. **Check BVar indices**: Print the binder stack and verify each `.bvar N` points to the right binder.
2. **Test subexpressions**: Use `#eval infer env term` on smaller subterms to find where inference fails.
3. **Check whnf**: Use `#eval whnf env term` to see if delta/iota reduction produces the expected form.
4. **Check defEq**: Use `#eval defEq env a b` to verify the inferred type matches the expected type.
5. **Common mistakes**:
   - Off-by-one BVar index after adding/removing a binder
   - Forgetting that entering a lambda/forall shifts all outer BVars up by 1
   - Using the wrong universe level in `Nat.rec` applications
   - Missing `let` bindings that shift BVar numbering

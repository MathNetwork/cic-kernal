# Dual Kernel Synchronization

## TreeKernel vs HypergraphKernel Differences

| Aspect | TreeKernel | HypergraphKernel |
|--------|-----------|-------------|
| Identity type | `String` | `UInt64` (content hash) |
| Environment | `Env` (name-keyed map) | `AstroNet` (hash-keyed map) |
| Const constructor | `.const "Nat" []` | `.const hNat []` |
| Declaration lookup | by string name | by hash |
| Iota reduction | Hardcoded pattern match on "Nat.rec" | Generic via `RecursorInfo` + `RecRule` |
| DefEq fast path | None (always whnf + structural) | Hash comparison first, then whnf if mismatch |
| Recursor info | Not needed (hardcoded) | `RecursorInfo` required for each recursor |

## RecursorInfo Design (HypergraphKernel only)

```lean
structure RecRule where
  constructorHash : UInt64  -- hash of the constructor this rule matches
  nFields : Nat             -- number of fields the constructor has

structure RecursorInfo where
  numParams : Nat := 0      -- number of type parameters (before motive)
  numMinors : Nat := 0      -- number of minor premises (one per constructor)
  numIndices : Nat := 0     -- number of index arguments (after minors, before major)
  rules : List RecRule := []
```

For Nat.rec: `numParams = 1` (motive), `numMinors = 2` (zero case, succ case), `numIndices = 0`.
For Eq.rec: `numParams = 3` (alpha, a, motive), `numMinors = 1` (refl_case), `numIndices = 1` (b).

## Checklist for Adding a New Inductive Type

1. **TreeKernel**: Define type expr, constructor exprs, recursor expr and add to hardcoded iota in `whnf`.
2. **HypergraphKernel**: Define the same exprs using hashes. Create `RecursorInfo` with correct params/minors/indices and `RecRule` entries. Register with `.recursor info` kind.
3. **Examples**: Add declarations to both `LeanSetup.lean` and `AstroSetup.lean`. Update the registration chain (env/net numbering).
4. **Test**: Add paired example files `LeanX.lean` / `AstroX.lean` testing the new type.
5. **CLAUDE.md**: Update the Verified Declarations table.
6. **Build**: `lake clean && lake build` must pass with 0 errors.

## Synchronization Rule

When modifying kernel logic (subst, whnf, infer, defEq, check):
- Make the change in TreeKernel first.
- Mirror it in HypergraphKernel, adapting only the identity mechanism.
- Run `lake build` to verify both kernels and all examples still pass.
- Never commit a change to one kernel without the corresponding change to the other.

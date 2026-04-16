# TreeKernel

A standard name-based CIC kernel in Lean 4. Serves as a baseline comparison for HypergraphKernel.

## Key difference from HypergraphKernel

- `Const` carries `String` (name), not `UInt64` (hash)
- `defEq` has no hash fast path — always whnf then structural comparison
- `check` only registers declarations, no nerve generation
- No Hash.lean, AstroNerve.lean, AstroNet.lean, or Shatter.lean

## Files

| File | Description |
|------|-------------|
| `Expr.lean` | CIC expression type (6 constructors, const uses String) |
| `Decl.lean` | Declaration kinds and structure |
| `Env.lean` | Environment: HashMap String Decl |
| `Kernel.lean` | subst, whnf, infer, defEq, check |

## Run

```bash
lake build && lake exe standardkernel
```

Output: 5 verified declarations.

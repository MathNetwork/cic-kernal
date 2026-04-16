# HypergraphKernel

A content-addressed CIC kernel in Lean 4. Replaces string names with content hashes.

## Key difference from TreeKernel

- `Const` carries `UInt64` (content hash), not `String` (name)
- `defEq` has an O(1) hash fast path before structural comparison
- `check` generates content-addressed nerves (AstroNerve) alongside type-checking
- `shatter` decomposes verified expressions into Store(1,1): atom nerves + edge nerves

## Files

| File | Description |
|------|-------------|
| `Expr.lean` | CIC expression type (6 constructors, const uses UInt64) |
| `Hash.lean` | Merkle-style hashing for Expr trees |
| `AstroNerve.lean` | The sole primitive: (hash, ref, record) |
| `AstroNet.lean` | Environment + nerve store |
| `Decl.lean` | Declaration kinds and structure |
| `Kernel.lean` | subst, whnf, infer, defEq, check |
| `Shatter.lean` | Expr tree -> Store(1,1) decomposition |

## Run

```bash
lake build && lake exe astrocore
```

Output: 5 verified declarations + 39 nerves (19 atoms + 20 edges).

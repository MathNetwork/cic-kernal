# Example File Conventions

## File Naming

Examples always come in pairs: `LeanX.lean` and `AstroX.lean`. They test the same functionality with both kernels.

| File pair | Tests |
|-----------|-------|
| `LeanExpr` / `AstroExpr` | Each Expr constructor's infer (empty env) |
| `LeanCheck` / `AstroCheck` | Declaration registration chain |
| `LeanInfer` / `AstroInfer` | Const lookup with populated env |
| `LeanWhnf` / `AstroWhnf` | Beta, delta, zeta, iota reduction |
| `LeanDefEq` / `AstroDefEq` | Definitional equality |
| `LeanIota` / `AstroIota` | Nat.add computation |
| `LeanLet` / `AstroLet` | LetE (zeta reduction) |
| `LeanLit` / `AstroLit` | Literal expressions |
| `LeanEq` / `AstroEq` | Eq type + theorem proofs |

## Setup Modules

**Do not copy-paste registration chains into individual example files.**

- `LeanSetup.lean`: Provides `env0`-`env8`, all type/value definitions, and helper functions (`mkAdd`, `mkSucc`, `mkEq`, `mkRefl`, `mkEqRec`).
- `AstroSetup.lean`: Provides `net0`-`net8`, hash constants (`hNat`, `hZero`, `hSucc`, `hRec`, `hNatAdd`, `hEq`, `hEqRefl`, `hEqRec`), `RecursorInfo` values, and hash-based helper functions.

Usage:
```lean
import Examples.LeanSetup    -- for Lean examples
import Examples.AstroSetup   -- for Astro examples
```

Exceptions:
- `LeanExpr` / `AstroExpr`: Import kernel directly, define their own empty env.
- `LeanLit` / `AstroLit`: Import Setup but define additional `String` declaration locally.

## File Structure Template

```lean
import Examples.LeanSetup

-- File description comment

-- === Test Section Name ===
#eval someFunction env5 someExpr
-- expected: description of expected result
```

## Result Consistency

If `LeanX.lean` produces result R for test T, then `AstroX.lean` must produce an equivalent result (modulo String to UInt64 key difference).

When adding a new test:
1. Write it in the Lean file first with expected result comments.
2. Translate to the Astro file, replacing string names with hash constants.
3. Verify both produce equivalent results via `lake build`.

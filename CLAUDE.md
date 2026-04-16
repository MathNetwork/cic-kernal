# CLAUDE.md -- AstroCore Project Conventions

## Absolute Prohibitions

- **No python, python3, python -c** — ever, for any purpose
- **No sed, awk** for file content processing
- **No bash scripts** for data processing or text transformation
- **No cat | pipe** to any parser or processor

All data validation must be written in Lean. All file modifications use Edit/str_replace tools only.
If JSON data needs processing, write it in Lean. Violating these rules requires immediate stop.

## Project Overview

AstroCore contains two parallel CIC kernel implementations in Lean 4:
- **TreeKernel**: name-based identity (`String`)
- **HypergraphKernel**: content-hash-based identity (`UInt64`)

Goal: demonstrate CIC typing judgments are invariant under identity mechanism substitution.

## Repository Structure

```
AstroCore/
├── TreeKernel/       # Name-based CIC kernel
├── HypergraphKernel/      # Hash-based CIC kernel
├── Examples/Examples/ # Comparative test suite (Lean/Astro pairs)
│   ├── LeanSetup.lean / AstroSetup.lean  # Shared registration chains
│   └── Lean*.lean / Astro*.lean          # Test files
├── .claude/skills/   # Detailed conventions (see below)
└── docs/             # Documentation and analysis
```

## Cardinal Rules

1. **Dual kernel invariant**: Every TreeKernel change needs a matching HypergraphKernel change. Only permitted differences: identity mechanism (String vs UInt64), hash computation, RecursorInfo-based iota (Astro) vs hardcoded iota (Lean).
2. **Build-is-verification**: `lake build` compiles all Examples. Any `check` returning `none` causes `.get!` to panic. Green build = all declarations verified.
3. **No dead code**: Every definition used, every import necessary, every file purposeful.
4. **No `sorry`**: Never use `sorry` anywhere in the codebase.

## Build Commands

```bash
lake build                    # Build everything (kernels + examples)
lake build TreeKernel         # Build name-based kernel only
lake build HypergraphKernel        # Build hash-based kernel only
lake build Examples           # Build all examples
lake clean && lake build      # Full rebuild
```

## Key Lean Conventions

- **File layout**: Copyright header, imports, `/-! -/` module docstring, then definitions.
- **Naming**: Types `UpperCamelCase`, functions `camelCase`, theorems `snake_case`.
- **Formatting**: 100 char lines, 2-space indent, `fun` not `lambda`, `<|` not `$`, `:=` at end of line.
- **Types**: All argument types explicit, return types always specified.
- **Docstrings**: Every `def`, `structure`, `inductive` must have `/-- -/` docstring.
- **Function length**: Max 40 lines per function; extract helpers if longer.
- **BVar annotations**: Every `.bvar N` must have a comment identifying its referent.
- **Helper functions**: Use `mkEq`, `mkRefl`, `mkAdd`, `mkSucc`, `mkEqRec` -- never hand-write deep Expr trees.

See `.claude/skills/lean-style.md` for detailed formatting rules and examples.

## Kernel-Specific Rules

- **HypergraphKernel**: Always use `RecursorInfo` + `RecRule` for iota reduction. Never hardcode constructor matching.
- **TreeKernel**: Hardcoded iota is acceptable as the comparison baseline; each hardcoded recursor must comment the generic HypergraphKernel equivalent.
- **Proof terms**: Annotate every BVar. Use helper functions. See `.claude/skills/proof-term.md`.
- **New inductive types**: Follow the checklist in `.claude/skills/dual-kernel.md`.

## Anti-Patterns (Do NOT)

- Copy-paste registration chains across Example files (use Setup modules)
- Write BVar indices without comments
- Change one kernel without changing the other
- Write functions longer than 40 lines
- Leave unused imports
- Use `partial def` without a termination comment
- Commit with `lake build` failures

## Verified Declarations

| Name | Kind | Env/Net |
|------|------|---------|
| Nat | constructor | env1/net1 |
| Nat.zero | constructor | env2/net2 |
| Nat.succ | constructor | env3/net3 |
| Nat.rec | recursor | env4/net4 |
| Nat.add | definition | env5/net5 |
| Eq | axiom | env6/net6 |
| Eq.refl | constructor | env7/net7 |
| Eq.rec | recursor | env8/net8 |
| Nat.add_zero | theorem | env9/net9 |
| Nat.add_succ | theorem | env10/net10 |
| zero_add | theorem | env11/net11 |
| succ_add | theorem | env12/net12 |
| Eq.symm | theorem | env13/net13 |
| Eq.trans | theorem | env14/net14 |
| Nat.add_comm | theorem | env15/net15 |

## Skill Files

- `.claude/skills/lean-style.md` -- Detailed Lean style guide
- `.claude/skills/dual-kernel.md` -- Dual kernel synchronization rules
- `.claude/skills/proof-term.md` -- Proof term construction guide
- `.claude/skills/examples.md` -- Example file conventions

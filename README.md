# CIC Type-Checking as Growing a Content-Addressed Hypergraph

A CIC kernel that performs type-checking directly on a content-addressed directed hypergraph. Every intermediate expression produced during type-checking becomes a permanent node in the hypergraph. The hypergraph only grows.

[![Live Demo](https://img.shields.io/badge/Live_Demo-cic--kernal.vercel.app-e8a860?style=for-the-badge&logo=vercel&logoColor=white)](https://cic-kernal.vercel.app/)
[![Zulip](https://img.shields.io/badge/Zulip-QED_Infra-e8a860?style=for-the-badge&logo=zulip&logoColor=white)](https://qedinfra.zulipchat.com)

## What this is

Two CIC kernels, implemented in Lean 4, verified on the same 15 declarations from `Nat` through `Nat.add_comm`:

- **TreeKernel** — A traditional kernel. Takes expression trees as input, produces expression trees as output. Intermediate results are temporary values, discarded after use.
- **HypergraphKernel** — The hypergraph kernel. Takes an `AstroNet` (a content-addressed set of nerves) as input, returns a larger `AstroNet` as output. Every substitution result, every reduced term, every inferred type becomes a permanent nerve in the store.

Both kernels accept the same declarations. The tree kernel's correctness is verified at compile time via `native_decide`. The hypergraph kernel's correctness is verified at runtime, with `AstroNet.validate` confirming that the structural conditions of the hypergraph hold on the final store.

## Repository structure

```
GenericKernel/          Traditional CIC kernel (expression trees, parameterized over key type)
TreeKernel/             GenericKernel instantiated at Key = String
HypergraphKernel/
  HyperKernel.lean      The hypergraph kernel (279 lines, zero partial def)
  NerveOps.lean         Record string parsing
  AstroNerve.lean       Nerve: (hash, ref, record)
  AstroNet.lean         Hypergraph: HashMap UInt64 AstroNerve
Examples/
  Tests/HyperTest.lean  15 declarations built and checked on the hypergraph
  Verify/               native_decide proofs (StoreEquivalence)
  Data/                 treeenv.json (15 expression trees), cahypergraph.json (612 nerves)
Theory/                 Depth filtration, stabilization, cycle theorems (Mathlib, zero sorry)
```

## Build and run

```bash
lake build              # Build everything
lake exe hypertest      # Run hypergraph kernel verification (15/15, validate = true)
```

For the Theory module:
```bash
cd Theory && lake exe cache get && lake build
```

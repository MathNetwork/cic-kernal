# AstroCore: CIC Expressions as a Content-Addressed Directed Hypergraph

**Technical Notes**

Xinze Li

April 2026

---

## 1. Observation

CIC expressions naturally form a directed hypergraph in the sense of Barkeshli–Douglas–Freedman (arXiv:2604.06107). Each sub-expression is simultaneously an element of the hypergraph and a hyperedge connecting its children. The constructor arity of each CIC expression determines its width — a structural invariant that requires no artificial encoding.

When this hypergraph is made content-addressable (identity determined by content, not by name), two properties emerge: (1) identical sub-expressions are automatically identified, and (2) type-checking is invariant under the choice of identity mechanism. These notes document a small implementation and verification of this observation.

---

## 2. BDF directed hypergraph and CIC

Barkeshli–Douglas–Freedman define a directed hypergraph as a structure (S, U, H, E, T_E) with a depth function d(s) and inductive closure. Their framework arises in the context of topological quantum field theory. We observe that it instantiates directly onto CIC expressions.

### Mapping

| BDF | AstroNet (CIC instantiation) |
|---|---|
| S (source vertices) | Atoms: BVar, Sort, Const, Lit (width 0) |
| H (hyperedges) | Compound expressions: App, Lam, ForallE, LetE (width > 0) |
| E = S ∪ H | All nerves |
| T_E (incidence / target map) | `ref` — ordered list of child hashes |
| d(s) (depth function) | `depthFilt` — expression nesting depth |
| Inductive closure | Closure axiom: every hash in `ref` exists in the store |

### Width is constructor arity

Width is not assigned — it is read off from the CIC grammar:

```
width 0:  BVar n, Sort u, Const k ls, Lit l       (atoms)
width 1:  App f a, Lam ty body, ForallE ty body    (binary)
width 2:  LetE ty val body                         (ternary)
```

This means the BDF degree decomposition E = E₀ ∪ E₁ ∪ E₂ corresponds exactly to the CIC constructor classification. No design choice is involved.

### Depth filtration

Define A(0) = atoms, A(m+1) = { e | ∀ r ∈ ref(e), r ∈ A(m) }. We prove:

- `depthFilt_mono`: A(m) ⊆ A(m+1) — the filtration is monotone
- `depthFilt_stabilizes`: for a finite store, there exists N such that A(N) = A(N+1)

These correspond to BDF's depth function properties. In CIC, depth measures how deeply nested an expression is: `Nat` has depth 0, `App(succ, zero)` has depth 1, a proof term invoking Nat.rec has higher depth.

---

## 3. Content-addressing

Each nerve is a triple (hash, ref, record):

```
hash = H(record)                — identity determined by content
ref  = [child₁_hash, ..., childₖ_hash]  — structural references
record = string encoding of the expression  — content
```

Content-addressing adds two properties not present in BDF's abstract framework:

1. **Automatic identification.** Two structurally identical sub-expressions have the same hash and are the same nerve. In a traditional expression tree, `Const Nat` appearing three times in a type signature is three separate nodes. In the content-addressed hypergraph, it is one nerve referenced three times.

2. **Identity-independence.** `hash = H(record)` does not depend on names. The same mathematical content in different projects, different files, or different naming conventions produces the same nerve.

`ref` is independent of `hash` — it records structural relationships but does not contribute to identity. This means references can be added to a nerve without changing its identity, supporting incremental knowledge construction.

---

## 4. Store Equivalence

### Setup

GenericKernel is parameterized over a Key type. Five functions (check, infer, whnf, defEq, addDecl) operate generically. Two instantiations:

- **TreeKernel**: Key = String (name-based identity, traditional)
- **HypergraphKernel**: Key = UInt64 (content-based identity, hash)

Both share the same check/infer/whnf/defEq code. They differ only in how `Const` nodes reference declarations.

### Verification

On a concrete environment of 15 declarations (Nat, Nat.zero, Nat.succ, Nat.rec, Nat.add, Eq, Eq.refl, Eq.rec, add_zero, add_succ, zero_add, succ_add, Eq.symm, Eq.trans, Nat.add_comm):

```lean
theorem lean_build_succeeds  : buildEnv (Key := String) ... = true := by native_decide
theorem astro_build_succeeds : buildEnv (Key := UInt64) ... = true := by native_decide
theorem lean_astro_same_size : ... = true := by native_decide
```

Plus functoriality of key translation:

```lean
theorem mapExpr_id : mapExpr id e = e
theorem mapExpr_comp : mapExpr f (mapExpr g e) = mapExpr (f ∘ g) e
```

Zero sorry. This is concrete verification, not a general proof. A general proof would require injectivity of the hash function.

### Interpretation

The observation is simple: CIC typing rules reference declarations by key but never inspect the key's structure. Replacing String with UInt64 cannot affect which terms are accepted. GenericKernel makes this explicit by parameterization; native_decide confirms it on a concrete instance.

---

## 5. Deduplication data

After type-checking, the Shatter function decomposes each expression into nerves. Data from actual kernel execution:

| Declaration | Tree nodes | Nerves | Dedup rate |
|---|---|---|---|
| Nat.add_comm | 226 | 91 | 59% |
| succ_add | 142 | 66 | 53% |
| add_zero | 96 | 44 | 54% |
| zero_add | 96 | 42 | 56% |
| **Total (all 15)** | **825** | **280** | **66%** |

In the add_comm proof term: `Nat.add` appears 19 times, `Nat.succ` 11 times, `Nat` 10 times — each stored as one nerve.

This deduplication is a direct consequence of content-addressing. It is not novel — Lean 4's `ShareCommon.shareCommon'` achieves the same sharing as a post-hoc optimization. The difference is that in the BDF hypergraph, deduplication is a structural property (the injectivity axiom), not an optimization pass.

---

## 6. ExprWithHash — O(1) equality fast path

Pre-computed hashes enable constant-time definitional equality for cache hits:

| Depth | GenericKernel.defEq | Hash comparison | Speedup |
|---|---|---|---|
| 100 | 423 ms | 0.32 ms | 1,322× |
| 1,000 | 4,243 ms | 0.37 ms | 11,467× |
| 10,000 | 43,306 ms | 0.30 ms | 144,353× |

Lean 4 already caches hashes on Expr for the same purpose. We reproduce this in our simplified kernel.

---

## 7. Related work

### BDF directed hypergraphs (Barkeshli–Douglas–Freedman, 2026)

The mathematical framework that AstroNet instantiates. BDF define directed hypergraphs with depth functions and inductive closure in the context of topological quantum field theory. They do not discuss CIC, content-addressing, or implementation. Our contribution is observing that CIC expressions are a natural instance of their framework.

### Lean 4

Lean 4's Expr type has cached hashes at construction. `ShareCommon.shareCommon'` deduplicates common subterms as a post-hoc pass. `.olean` files preserve DAG structure. Identity is name-based (`Const` carries a `Name`). Lean does not formalize the sharing or provide axioms for it.

### Yatima (argumentcomputer/yatima)

Yatima implements nameless content-addressing for Lean 4 expressions, with each expression receiving a unique hash independent of naming. It includes its own Lean 4 kernel and targets Lurk for zkSNARK verification. Yatima embeds ASTs as IPLD objects for sharing over IPFS.

Yatima is the closest prior work on content-addressing for CIC. The key difference: Yatima's data model is a content-addressed tree/DAG. Ours is a content-addressed directed hypergraph in the BDF sense, with width, depth filtration, and the nerve abstraction that unifies nodes and hyperedges. Yatima does not have this mathematical structure.

### Unison

A content-addressed programming language (since 2013). Functions identified by hash of their syntax tree. No dependent types, no formal verification, no hypergraph structure.

### lean4lean (Carneiro)

Re-implementation of the Lean 4 kernel in Lean 4 as an external checker. Includes initial type theory formalization. Far more comprehensive than our 400-line kernel.

### MetaCoq

Formalization of CIC in Coq with a verified type-checker. Does not address content-addressing or hypergraph structure.

---

## 8. What these notes contribute

1. **BDF instantiation.** CIC expressions naturally form a BDF directed hypergraph. Width = constructor arity. Depth filtration = expression nesting. This connection has not been observed previously, to our knowledge.

2. **Store Equivalence verification.** Concrete mechanized verification that CIC type-checking is invariant under identity mechanism substitution. Not a deep theorem, but a clean formal statement that has not appeared elsewhere.

3. **Quantified deduplication.** Measurements from actual kernel execution: 825 tree nodes → 280 nerves across 15 declarations.

These notes do not claim novelty in content-addressing for dependent type theories (Yatima), hash consing for expressions (Lean 4), or CIC kernel implementation (lean4lean, MetaCoq). The contribution is the observation that CIC and BDF directed hypergraphs are naturally compatible, and a small verification of this compatibility.

---

## 9. Open questions

1. Does depth filtration on CIC expressions produce nontrivial persistent homology? What are the Betti numbers of a Mathlib-scale nerve store?

2. Can Store Equivalence be proved in general (for all well-typed environments), not just for 15 declarations?

3. Does the BDF structure on CIC expressions have consequences for proof search, autoformalization, or library refactoring?

4. How does the nerve hypergraph relate to the dependency network analyzed in the Mathlib paper (308K nodes, NMI 0.34)?

---

## 10. Repository

**GitHub:** https://github.com/MathNetwork/cic-kernal

```
AstroCore/
├── GenericKernel/    — Parameterized CIC kernel (397 lines)
├── TreeKernel/       — Key = String
├── HypergraphKernel/      — Key = UInt64, ExprWithHash, Shatter
├── Theory/           — AstroNerve/AstroNet definitions (Mathlib-compatible)
├── Examples/         — StoreEquivalence, Benchmark, Diagnostics, TraceRun
└── web/              — Interactive visualization
```

Apache 2.0.

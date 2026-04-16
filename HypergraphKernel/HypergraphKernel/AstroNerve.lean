/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/

/-!
# AstroNerve: Astrolabe's Sole Primitive

An `AstroNerve` is the universal storage unit of the Astrolabe system.
It consists of a content-addressed `hash`, a `ref` list pointing to
other nerves, and a `record` string holding serialized content.
The hash equals `H(record)`; `ref` does not participate in hashing.

## Main Definitions

- `AstroNerve`: The sole primitive of Astrolabe — `(hash, ref, record)`.
-/

/-- The sole primitive of Astrolabe: a content-addressed triple `(hash, ref, record)`. -/
structure AstroNerve where
  hash   : UInt64       -- H(record)
  ref    : List UInt64  -- list of hashes pointing to other nerves
  record : String       -- serialized content
  deriving Repr, BEq

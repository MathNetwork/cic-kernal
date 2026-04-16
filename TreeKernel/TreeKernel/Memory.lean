/-
Copyright (c) 2026 Xinze Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xinze Li
-/
import TreeKernel.Defs

/-!
# JSON Serialization for TreeKernel

JSON dump utilities for the name-based `Env`. Serializes `Level`, `Expr`,
`DeclKind`, `Decl`, and the full `Env` to JSON strings.

## Main Definitions

- `levelToJson`: Serialize a universe level to JSON.
- `exprToJson`: Serialize a CIC expression to JSON.
- `declToJson`: Serialize a declaration to JSON.
- `envToJson`: Serialize the entire environment to JSON.
-/

open TreeKernel

/-- Serialize a `Level` to a JSON-compatible string. -/
partial def levelToJson : Level → String
  | .zero => "0"
  | .succ l => s!"(succ {levelToJson l})"
  | .max a b => s!"(max {levelToJson a} {levelToJson b})"
  | .imax a b => s!"(imax {levelToJson a} {levelToJson b})"
  | .param n => s!"(param {n})"

/-- Serialize an `Expr` to a JSON string. -/
partial def exprToJson : Expr → String
  | .bvar n => s!"\{\"bvar\": {n}}"
  | .sort u => s!"\{\"sort\": \"{levelToJson u}\"}"
  | .const name levels =>
      let ls := String.intercalate ", " (levels.map (s!"\"{levelToJson ·}\""))
      s!"\{\"const\": \"{name}\", \"levels\": [{ls}]}"
  | .app f a => s!"\{\"app\": [{exprToJson f}, {exprToJson a}]}"
  | .lam ty body => s!"\{\"lam\": [{exprToJson ty}, {exprToJson body}]}"
  | .forallE ty body => s!"\{\"forallE\": [{exprToJson ty}, {exprToJson body}]}"
  | .letE ty val body => s!"\{\"letE\": [{exprToJson ty}, {exprToJson val}, {exprToJson body}]}"
  | .lit (.natVal n) => s!"\{\"natLit\": {n}}"
  | .lit (.strVal s) => s!"\{\"strLit\": \"{s}\"}"

/-- Serialize a `DeclKind` to a JSON string. -/
def declKindToJson : DeclKind → String
  | .axiom => "\"axiom\""
  | .constructor => "\"constructor\""
  | .recursor _ => "\"recursor\""
  | .definition => "\"definition\""

/-- Serialize a `Decl` to a JSON string. -/
def declToJson (d : Decl) : String :=
  let v := match d.value with
    | some val => exprToJson val
    | none => "null"
  s!"\{\"kind\": {declKindToJson d.kind}, \"type\": {exprToJson d.type}, \"value\": {v}}"

/-- Serialize the entire `Env` to a JSON string with all declarations. -/
def Env.toJson (env : Env) : String :=
  let entries := env.decls.toList.map fun (name, decl) =>
    s!"\{\"name\": \"{name}\", \"decl\": {declToJson decl}}"
  let body := String.intercalate ", " entries
  s!"\{\"declarations\": [{body}]}"

import HypergraphKernel

open HypergraphKernel

def natType : Expr := .sort Level.one
def hNat : UInt64 := "Sort(Ls(L0))".hash
def zeroType : Expr := .const hNat []
def hZero : UInt64 := s!"Const({hNat}, [])".hash
def succType : Expr := .forallE (.const hNat []) (.const hNat [])
def hSucc : UInt64 := s!"ForallE({hZero}, {hZero})".hash
def recType : Expr :=
  .forallE (.forallE (.const hNat []) (.sort (.param 0)))
    (.forallE (.app (.bvar 0) (.const hZero []))
      (.forallE
        (.forallE (.const hNat [])
          (.forallE (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const hSucc []) (.bvar 1)))))
        (.forallE (.const hNat [])
          (.app (.bvar 3) (.bvar 0)))))
def hRec : UInt64 := (hashExpr recType).1
def addType : Expr := .forallE (.const hNat []) (.forallE (.const hNat []) (.const hNat []))
def hNatAdd : UInt64 := (hashExpr addType).1
def addValue : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.app (.app (.app (.app (.const hRec [Level.one])
        (.lam (.const hNat []) (.const hNat [])))
        (.bvar 1))
        (.lam (.const hNat []) (.lam (.const hNat []) (.app (.const hSucc []) (.bvar 0)))))
        (.bvar 0)))
def natRecInfo : RecursorInfo := {
  numParams := 1, numMinors := 2,
  rules := [{ constructorKey := hZero, nFields := 0 }, { constructorKey := hSucc, nFields := 1 }]
}

def main : IO Unit := do
  let mut env : Env UInt64 := Env.empty
  match check hNat natType none .constructor env with
  | some e => env := e; IO.println s!"✓ Nat"
  | none => IO.println "✗ Nat"; return
  match check hZero zeroType none .constructor env with
  | some e => env := e; IO.println s!"✓ Nat.zero"
  | none => IO.println "✗ Nat.zero"; return
  match check hSucc succType none .constructor env with
  | some e => env := e; IO.println s!"✓ Nat.succ"
  | none => IO.println "✗ Nat.succ"; return
  match check hRec recType none (.recursor natRecInfo) env with
  | some e => env := e; IO.println s!"✓ Nat.rec"
  | none => IO.println "✗ Nat.rec"; return
  match check hNatAdd addType (some addValue) .definition env with
  | some e => env := e; IO.println s!"✓ Nat.add"
  | none => IO.println "✗ Nat.add"; return
  IO.println s!"env size: {env.size}"

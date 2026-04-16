import Examples.Setup.NerveSetup
open HypergraphKernel

instance : Inhabited (Expr UInt64) := ⟨.lit (.natVal 0)⟩

partial def mkDeepNat (n : Nat) : Expr UInt64 :=
  match n with
  | 0 => .const hZero []
  | n + 1 => .app (.const hSucc []) (mkDeepNat n)

@[noinline] def benchLoop (f : Unit → Bool) (iters : Nat) : IO Nat := do
  let ref ← IO.mkRef (0 : Nat)
  for _ in List.range iters do
    if f () then ref.modify (· + 1)
  ref.get

def timeIt (label : String) (act : IO Nat) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  IO.println s!"{label} {((t1 - t0).toFloat / 1000000.0)}ms"
  return r

#eval show IO Unit from do
  for depth in [100, 1000, 10000] do
    let e1 := mkDeepNat depth
    let e2 := mkDeepNat depth
    IO.println s!"--- depth={depth}, 1000 iterations ---"
    let _ ← timeIt "GenericKernel.defEq " (benchLoop (fun _ => GenericKernel.defEq env8 e1 e2) 1000)
    let _ ← timeIt "defEq               " (benchLoop (fun _ => defEq env8 e1 e2) 1000)

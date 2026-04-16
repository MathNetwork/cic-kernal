import Std
import HypergraphKernel.AstroNerve

open Std

structure AstroNet where
  nerves : HashMap UInt64 AstroNerve
  deriving Repr

instance : Inhabited AstroNet where
  default := { nerves := {} }

def AstroNet.empty : AstroNet := { nerves := {} }

def AstroNet.add (s : AstroNet) (n : AstroNerve) : AstroNet :=
  { s with nerves := s.nerves.insert n.hash n }

def AstroNet.get (s : AstroNet) (h : UInt64) : Option AstroNerve :=
  s.nerves.get? h

def AstroNet.size (s : AstroNet) : Nat := s.nerves.size

def AstroNet.validate (net : AstroNet) : Bool :=
  let nerveList := net.nerves.toList.map (·.2)
  let ax1 := nerveList.all fun n =>
    if n.ref.length == 1 then n.ref.head! == n.hash else true
  let ax3 := nerveList.all fun n =>
    n.ref.all (net.nerves.contains ·)
  let ax4 := nerveList.all fun n =>
    if n.ref.length > 1 then !n.ref.contains n.hash else true
  ax1 && ax3 && ax4

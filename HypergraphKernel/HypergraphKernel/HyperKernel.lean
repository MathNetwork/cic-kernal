import HypergraphKernel.NerveOps
open HypergraphKernel

def listGet? (l : List α) (n : Nat) : Option α :=
  match l, n with
  | a :: _, 0 => some a
  | _ :: rest, n + 1 => listGet? rest n
  | [], _ => none
structure ParsedRecInfo where
  numParams : Nat
  numMinors : Nat
  numIndices : Nat
  rules : List (UInt64 × Nat)
def parseRecInfo (record : String) : Option ParsedRecInfo :=
  if !record.startsWith "Decl(recursor," then none else
  let c := String.ofList ((record.drop 14).toString.toList.dropLast)
  match c.splitOn "," with
  | np :: nm :: ni :: rest =>
    some { numParams := np.toNat!, numMinors := nm.toNat!, numIndices := ni.toNat!,
           rules := rest.filterMap fun p =>
             match p.splitOn ":" with | [k, n] => some (k.toNat!.toUInt64, n.toNat!) | _ => none }
  | _ => none
def findRule (rules : List (UInt64 × Nat)) (ck : UInt64) (i : Nat := 0) : Option (Nat × Nat) :=
  match rules with
  | [] => none
  | (k, nf) :: rest => if k == ck then some (i, nf) else findRule rest ck (i + 1)
def mkAtomNerve (net : AstroNet) (record : String) : (UInt64 × AstroNet) :=
  let h := record.hash
  match net.get h with
  | some _ => (h, net)
  | none => (h, net.add { hash := h, ref := [h], record })
def mkNerve (net : AstroNet) (record : String) (refs : List UInt64) : (UInt64 × AstroNet) :=
  let h := record.hash
  match net.get h with
  | some _ => (h, net)
  | none => (h, net.add { hash := h, ref := refs, record })
def binderTag (tag : NerveTag) : String := if tag == .lam then "Lam" else "ForallE"
def shiftNerve (net : AstroNet) (h : UInt64) (cutoff amount fuel : Nat) : (UInt64 × AstroNet) :=
  match fuel with
  | 0 => (h, net)
  | fuel + 1 =>
  if amount == 0 then (h, net) else
  match net.get h with
  | none => (h, net)
  | some n => match n.tag with
    | .bvar =>
      let i := parseBVarIdx n.record
      if i >= cutoff then mkAtomNerve net s!"BVar({i + amount})" else (h, net)
    | .sort | .const | .lit | .letE => (h, net)
    | .app =>
      let (f, net) := shiftNerve net n.ref[0]! cutoff amount fuel
      let (a, net) := shiftNerve net n.ref[1]! cutoff amount fuel
      if f == n.ref[0]! && a == n.ref[1]! then (h, net)
      else mkNerve net s!"App({f}, {a})" [f, a]
    | .lam | .forallE =>
      let (t, net) := shiftNerve net n.ref[0]! cutoff amount fuel
      let (b, net) := shiftNerve net n.ref[1]! (cutoff + 1) amount fuel
      if t == n.ref[0]! && b == n.ref[1]! then (h, net)
      else mkNerve net s!"{binderTag n.tag}({t}, {b})" [t, b]
def substNerve (net : AstroNet) (bodyH argH : UInt64) (idx fuel : Nat) : (UInt64 × AstroNet) :=
  match fuel with
  | 0 => (bodyH, net)
  | fuel + 1 =>
  match net.get bodyH with
  | none => (bodyH, net)
  | some n => match n.tag with
    | .bvar =>
      let i := parseBVarIdx n.record
      if i == idx then (argH, net)
      else if i > idx then mkAtomNerve net s!"BVar({i - 1})"
      else (bodyH, net)
    | .sort | .const | .lit | .letE => (bodyH, net)
    | .app =>
      let (f, net) := substNerve net n.ref[0]! argH idx fuel
      let (a, net) := substNerve net n.ref[1]! argH idx fuel
      if f == n.ref[0]! && a == n.ref[1]! then (bodyH, net)
      else mkNerve net s!"App({f}, {a})" [f, a]
    | .lam | .forallE =>
      let (t, net) := substNerve net n.ref[0]! argH idx fuel
      let (sa, net) := shiftNerve net argH 0 1 fuel
      let (b, net) := substNerve net n.ref[1]! sa (idx + 1) fuel
      if t == n.ref[0]! && b == n.ref[1]! then (bodyH, net)
      else mkNerve net s!"{binderTag n.tag}({t}, {b})" [t, b]
def sortLevelStr (record : String) : String :=
  String.ofList ((record.drop 5).toString.toList.dropLast)
def instLevel (lvl : String) (levels : List String) (fuel : Nat) : String :=
  match fuel with
  | 0 => lvl
  | fuel + 1 =>
  if lvl == "L0" then "L0"
  else if lvl.startsWith "Lp(" then
    let i := String.ofList ((lvl.drop 3).toString.toList.dropLast)
    (listGet? levels i.toNat!).getD lvl
  else if lvl.startsWith "Ls(" then
    s!"Ls({instLevel (String.ofList ((lvl.drop 3).toString.toList.dropLast)) levels fuel})"
  else if lvl.startsWith "Limax(" then
    let inner := String.ofList ((lvl.drop 6).toString.toList.dropLast)
    match inner.splitOn "," with
    | [a, b] => s!"Limax({instLevel a.trimAsciiStart.toString levels fuel},{instLevel b.trimAsciiStart.toString levels fuel})"
    | _ => lvl
  else lvl
def parseConstLevels (record : String) : List String :=
  let c := String.ofList ((record.dropWhile (· != '[') |>.drop 1).toString.toList.dropLast.dropLast)
  if c.isEmpty then [] else c.splitOn ", "
def instNerve (net : AstroNet) (h : UInt64) (levels : List String) (fuel : Nat) : (UInt64 × AstroNet) :=
  match fuel with
  | 0 => (h, net)
  | fuel + 1 =>
  if levels.isEmpty then (h, net) else
  match net.get h with
  | none => (h, net)
  | some n => match n.tag with
    | .sort =>
      let l := sortLevelStr n.record
      let l' := instLevel l levels fuel
      if l == l' then (h, net) else mkAtomNerve net s!"Sort({l'})"
    | .const =>
      let cls := parseConstLevels n.record
      let cls' := cls.map (instLevel · levels fuel)
      if cls == cls' then (h, net)
      else mkAtomNerve net s!"Const({parseConstKey n.record}, [{String.intercalate ", " cls'}])"
    | .app =>
      let (f, net) := instNerve net n.ref[0]! levels fuel
      let (a, net) := instNerve net n.ref[1]! levels fuel
      if f == n.ref[0]! && a == n.ref[1]! then (h, net)
      else mkNerve net s!"App({f}, {a})" [f, a]
    | .lam | .forallE =>
      let (t, net) := instNerve net n.ref[0]! levels fuel
      let (b, net) := instNerve net n.ref[1]! levels fuel
      if t == n.ref[0]! && b == n.ref[1]! then (h, net)
      else mkNerve net s!"{binderTag n.tag}({t}, {b})" [t, b]
    | _ => (h, net)
def getDeclNerve (net : AstroNet) (key : UInt64) : Option AstroNerve :=
  net.get s!"DeclKey({key})".hash
def unfoldAppsHH (net : AstroNet) (h : UInt64) (fuel : Nat) : (UInt64 × List UInt64) :=
  match fuel with
  | 0 => (h, [])
  | fuel + 1 =>
  match net.get h with
  | some n => if n.tag == .app then
      let (hd, args) := unfoldAppsHH net n.ref[0]! fuel; (hd, args ++ [n.ref[1]!])
    else (h, [])
  | none => (h, [])
def foldAppsH (net : AstroNet) (fn : UInt64) (args : List UInt64) : (UInt64 × AstroNet) :=
  match args with
  | [] => (fn, net)
  | a :: rest => let (h, net) := mkNerve net s!"App({fn}, {a})" [fn, a]; foldAppsH net h rest
def whnfNerve (net : AstroNet) (h : UInt64) (fuel : Nat) : (UInt64 × AstroNet) :=
  match fuel with
  | 0 => (h, net)
  | fuel + 1 =>
  match net.get h with
  | none => (h, net)
  | some nerve => match nerve.tag with
    | .app =>
      let fnH := nerve.ref[0]!; let argH := nerve.ref[1]!
      match net.get fnH with
      | none => (h, net)
      | some fnN =>
        if fnN.tag == .lam then
          let (r, net) := substNerve net fnN.ref[1]! argH 0 fuel
          whnfNerve net r fuel
        else
          let (headH, allArgs) := unfoldAppsHH net h fuel
          let fallback (net : AstroNet) : (UInt64 × AstroNet) :=
            let (fnH', net) := whnfNerve net fnH fuel
            if fnH' == fnH then (h, net) else
            let (newH, net) := mkNerve net s!"App({fnH'}, {argH})" [fnH', argH]
            whnfNerve net newH fuel
          match net.get headH with
          | none => fallback net
          | some headN =>
            if headN.tag != .const then fallback net else
            let key := parseConstKey headN.record
            match getDeclNerve net key with
            | none => fallback net
            | some decl =>
              match parseRecInfo decl.record with
              | some info =>
                let needed := info.numParams + info.numMinors + info.numIndices + 1
                if allArgs.length < needed then (h, net) else
                match listGet? allArgs (needed - 1) with
                | none => (h, net)
                | some targetH =>
                let (targetH', net) := whnfNerve net targetH fuel
                let (tHead, tArgs) := unfoldAppsHH net targetH' fuel
                match net.get tHead with
                | none => (h, net)
                | some tHN =>
                  if tHN.tag != .const then (h, net) else
                  match findRule info.rules (parseConstKey tHN.record) with
                  | none => (h, net)
                  | some (ruleIdx, nFields) =>
                  match listGet? allArgs (info.numParams + ruleIdx) with
                  | none => (h, net)
                  | some minorH => match nFields with
                    | 0 => whnfNerve net minorH fuel
                    | 1 => match listGet? tArgs 0 with
                      | none => (h, net)
                      | some nH =>
                        let recArgs := allArgs.take (info.numParams + info.numMinors)
                        let (rc, net) := foldAppsH net headH (recArgs ++ [nH])
                        let (a1, net) := mkNerve net s!"App({minorH}, {nH})" [minorH, nH]
                        let (r, net) := mkNerve net s!"App({a1}, {rc})" [a1, rc]
                        whnfNerve net r fuel
                    | _ => (h, net)
              | none =>
                if decl.ref.length > 2 then
                  let (r, net) := foldAppsH net decl.ref[2]! allArgs
                  whnfNerve net r fuel
                else fallback net
    | .const =>
      match getDeclNerve net (parseConstKey nerve.record) with
      | some d => if d.ref.length > 2 then whnfNerve net d.ref[2]! fuel else (h, net)
      | none => (h, net)
    | _ => (h, net)
mutual
def defEqNerve (net : AstroNet) (h1 h2 : UInt64) (fuel : Nat) : (Bool × AstroNet) :=
  match fuel with
  | 0 => (false, net)
  | fuel + 1 =>
  if h1 == h2 then (true, net) else
  let (h1', net) := whnfNerve net h1 fuel; let (h2', net) := whnfNerve net h2 fuel
  if h1' == h2' then (true, net) else
  match net.get h1', net.get h2' with
  | some n1, some n2 =>
    if n1.tag != n2.tag then (false, net) else match n1.tag with
    | .sort | .const | .lit => (n1.record == n2.record, net)
    | .bvar => (parseBVarIdx n1.record == parseBVarIdx n2.record, net)
    | .app | .lam | .forallE =>
      let (eq, net) := defEqNerve net n1.ref[0]! n2.ref[0]! fuel
      if !eq then (false, net) else defEqNerve net n1.ref[1]! n2.ref[1]! fuel
    | _ => (false, net)
  | _, _ => (false, net)
def inferNerve (net : AstroNet) (h : UInt64) (ctx : List UInt64) (fuel : Nat)
    : Option (UInt64 × AstroNet) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  match net.get h with
  | none => none
  | some n => match n.tag with
    | .bvar => (listGet? ctx (parseBVarIdx n.record)).map (·, net)
    | .sort => some (mkAtomNerve net s!"Sort(Ls({sortLevelStr n.record}))")
    | .const =>
      match getDeclNerve net (parseConstKey n.record) with
      | some d => some (instNerve net d.ref[1]! (parseConstLevels n.record) fuel)
      | none => none
    | .app => do
      let (ftH, net) ← inferNerve net n.ref[0]! ctx fuel
      let (ftH', net) := whnfNerve net ftH fuel
      let ft ← net.get ftH'
      guard (ft.tag == .forallE)
      let (r, net) := substNerve net ft.ref[1]! n.ref[1]! 0 fuel
      some (whnfNerve net r fuel)
    | .lam => do
      let (btyH, net) ← inferNerve net n.ref[1]! (n.ref[0]! :: ctx) fuel
      some (mkNerve net s!"ForallE({n.ref[0]!}, {btyH})" [n.ref[0]!, btyH])
    | .forallE => do
      let (tyTH, _) ← inferNerve net n.ref[0]! ctx fuel
      let (bdTH, net) ← inferNerve net n.ref[1]! (n.ref[0]! :: ctx) fuel
      let (tyTH', net) := whnfNerve net tyTH fuel
      let (bdTH', net) := whnfNerve net bdTH fuel
      let t1 ← net.get tyTH'; let t2 ← net.get bdTH'
      guard (t1.tag == .sort && t2.tag == .sort)
      some (mkAtomNerve net s!"Sort(Limax({sortLevelStr t1.record},{sortLevelStr t2.record}))")
    | _ => none
end
def checkNerve (net : AstroNet) (key typeH : UInt64) (valueH : Option UInt64)
    (kindRecord : String) (fuel : Nat := 10000) : Option AstroNet :=
  let declH := s!"DeclKey({key})".hash
  match valueH with
  | none =>
    some (net.add { hash := declH, ref := [key, typeH], record := kindRecord })
  | some valH => do
    let (inferredH, net) ← inferNerve net valH [] fuel
    let (eq, net) := defEqNerve net inferredH typeH fuel
    guard eq
    some (net.add { hash := declH, ref := [key, typeH, valH], record := kindRecord })

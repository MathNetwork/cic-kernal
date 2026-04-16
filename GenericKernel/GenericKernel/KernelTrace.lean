import GenericKernel.Kernel

instance : HasBuiltinKeys UInt64 where
  natKey := "Sort(Ls(L0))".hash
  stringKey := "Sort(Ls(L0))".hash

abbrev Trace := IO.Ref (Array (Expr UInt64))
abbrev E := Expr UInt64
abbrev En := Env UInt64

private def record (tr : Trace) (e : E) : IO E := do
  tr.modify (·.push e); return e

partial def substT (tr : Trace) (e arg : E) (depth : Nat := 0) : IO E := do
  match e with
  | .bvar n =>
      if n == depth then return arg
      else if n > depth then return .bvar (n - 1)
      else return .bvar n
  | .app f a =>
      let f' ← substT tr f arg depth
      let a' ← substT tr a arg depth
      record tr (.app f' a')
  | .lam ty body =>
      let ty' ← substT tr ty arg depth
      let body' ← substT tr body (shift arg 0 1) (depth + 1)
      record tr (.lam ty' body')
  | .forallE ty body =>
      let ty' ← substT tr ty arg depth
      let body' ← substT tr body (shift arg 0 1) (depth + 1)
      record tr (.forallE ty' body')
  | .letE ty val body =>
      let ty' ← substT tr ty arg depth
      let val' ← substT tr val arg depth
      let body' ← substT tr body (shift arg 0 1) (depth + 1)
      record tr (.letE ty' val' body')
  | e => return e

partial def whnfT (tr : Trace) (env : En) (e : E) : IO E := do
  match e with
  | .letE _ty val body =>
      let r ← substT tr body val
      let r ← record tr r
      whnfT tr env r
  | .app (.lam _ty body) arg =>
      let r ← substT tr body arg
      let r ← record tr r
      whnfT tr env r
  | .app f a =>
      let whole := Expr.app f a
      let whnfApp (f' : E) : IO E := do
        if f' == f then return whole else
        let e' ← record tr (Expr.app f' a)
        whnfT tr env e'
      let fallback : IO E := do whnfApp (← whnfT tr env f)
      let (head, args) := unfoldApps whole
      match head with
      | .const k levels =>
          match env.getDecl k with
          | some decl =>
              match decl.kind with
              | .recursor info =>
                  let needed := info.numParams + info.numMinors + info.numIndices + 1
                  if args.length >= needed then
                    match listGet? args (needed - 1) with
                    | none => fallback
                    | some target =>
                    let target' ← whnfT tr env target
                    let (tHead, tArgs) := unfoldApps target'
                    match tHead with
                    | .const ck _ =>
                        match findRuleIdx info.rules ck with
                        | some (ruleIdx, rule) =>
                            match listGet? args (info.numParams + ruleIdx) with
                            | none => fallback
                            | some minor =>
                            match rule.nFields with
                            | 0 => whnfT tr env minor
                            | 1 =>
                                match listGet? tArgs 0 with
                                | none => fallback
                                | some n =>
                                let recArgs := args.take (info.numParams + info.numMinors)
                                let recCall := applyArgs (Expr.const k levels) (recArgs ++ [n])
                                let r ← record tr (Expr.app (Expr.app minor n) recCall)
                                whnfT tr env r
                            | _ =>
                                let recArgs := args.take (info.numParams + info.numMinors)
                                let withFields := tArgs.foldl (fun acc x => Expr.app acc x) minor
                                let withRecs := tArgs.foldl (fun acc x =>
                                    let rc := applyArgs (Expr.const k levels) (recArgs ++ [x])
                                    Expr.app acc rc) withFields
                                let r ← record tr withRecs
                                whnfT tr env r
                        | none => fallback
                    | _ => fallback
                  else fallback
              | _ =>
                  match decl.value with
                  | some v =>
                      let e' := applyArgs (instantiateUnivParams v levels) args
                      let e' ← record tr e'
                      whnfT tr env e'
                  | none => fallback
          | none => fallback
      | _ => fallback
  | .const k levels =>
      match env.getDecl k with
      | some decl =>
          match decl.value with
          | some v =>
              let e' ← record tr (instantiateUnivParams v levels)
              whnfT tr env e'
          | none => return e
      | none => return e
  | e => return e

mutual
partial def inferT (tr : Trace) (env : En) (e : E) (ctx : List E := []) : IO (Option E) := do
  match e with
  | .bvar n => return listGet? ctx n
  | .sort u => return some (.sort (.succ u))
  | .const k levels =>
      match env.getDecl k with
      | some decl =>
          let ty := instantiateUnivParams decl.type levels
          let _ ← record tr ty
          return some ty
      | none => return none
  | .app f a =>
      match ← inferT tr env f ctx with
      | some fType =>
          let fType' ← whnfT tr env fType
          match fType' with
          | .forallE _paramType bodyType =>
              let r ← substT tr bodyType a
              let r ← record tr r
              let r ← whnfT tr env r
              return some r
          | _ => return none
      | none => return none
  | .lam ty body =>
      match ← inferT tr env body (ty :: ctx) with
      | some bodyType =>
          let r ← record tr (.forallE ty bodyType)
          return some r
      | none => return none
  | .forallE ty body =>
      match ← inferT tr env ty ctx, ← inferT tr env body (ty :: ctx) with
      | some tyType, some bodyType =>
          let tyType' ← whnfT tr env tyType
          let bodyType' ← whnfT tr env bodyType
          match tyType', bodyType' with
          | .sort u1, .sort u2 =>
              let r ← record tr (.sort (.imax u1 u2))
              return some r
          | _, _ => return none
      | _, _ => return none
  | .letE _ty val body =>
      match ← inferT tr env val ctx with
      | some valType =>
          if ← defEqT tr env valType _ty ctx then
            let r ← substT tr body val
            inferT tr env r ctx
          else return none
      | none => return none
  | .lit (.natVal _) => return some (.const HasBuiltinKeys.natKey [])
  | .lit (.strVal _) => return some (.const HasBuiltinKeys.stringKey [])

partial def defEqT (tr : Trace) (env : En) (a b : E) (ctx : List E := []) : IO Bool := do
  let a' ← whnfT tr env a
  let b' ← whnfT tr env b
  match a', b' with
  | .sort u1, .sort u2 => return u1 == u2
  | .const k1 ls1, .const k2 ls2 => return k1 == k2 && ls1 == ls2
  | .bvar n1, .bvar n2 => return n1 == n2
  | .app f1 a1, .app f2 a2 =>
      if ← defEqT tr env f1 f2 ctx then defEqT tr env a1 a2 ctx else return false
  | .lam t1 b1, .lam t2 b2 =>
      if ← defEqT tr env t1 t2 ctx then defEqT tr env b1 b2 (t1 :: ctx) else return false
  | .forallE t1 b1, .forallE t2 b2 =>
      if ← defEqT tr env t1 t2 ctx then defEqT tr env b1 b2 (t1 :: ctx) else return false
  | .letE t1 v1 b1, .letE t2 v2 b2 =>
      if ← defEqT tr env t1 t2 ctx then
        if ← defEqT tr env v1 v2 ctx then defEqT tr env b1 b2 (t1 :: ctx) else return false
      else return false
  | .lit l1, .lit l2 => return l1 == l2
  | _, _ => return false
end

def checkT (tr : Trace) (k : UInt64) (T : E) (v : Option E) (kind : DeclKind UInt64) (env : En) : IO (Option En) := do
  match v with
  | none =>
      let decl : Decl UInt64 := { kind := kind, type := T, value := none }
      return some (env.addDecl k decl)
  | some val =>
      match ← inferT tr env val with
      | some inferredT =>
          if ← defEqT tr env inferredT T then
            let decl : Decl UInt64 := { kind := kind, type := T, value := some val }
            return some (env.addDecl k decl)
          else return none
      | none => return none

import Examples.Setup.NerveSetup
open HypergraphKernel

-- === Tests ===

-- Check net sizes
#eval env6.size  -- 6
#eval env7.size  -- 7
#eval env8.size  -- 8

-- Infer Eq.refl type
#eval GenericKernel.infer env8 (.const hEqRefl [])

-- Construct: Eq.refl Nat Nat.zero  (proof that zero = zero)
-- This should have type: Eq Nat Nat.zero Nat.zero
def reflZero : Expr := .app (.app (.const hEqRefl []) (.const hNat [])) (.const hZero [])
#eval GenericKernel.infer env8 reflZero

-- Test Eq.rec iota reduction
-- Eq.rec Nat zero (fun _ => Nat) (succ zero) zero (Eq.refl Nat zero)
-- should reduce to: succ zero
def eqRecTest : Expr :=
  .app (.app (.app (.app (.app (.app (.const hEqRec [])
    (.const hNat []))          -- alpha = Nat
    (.const hZero []))         -- a = zero
    (.lam (.const hNat []) (.const hNat [])))  -- motive = fun _ => Nat
    (.app (.const hSucc []) (.const hZero [])))  -- refl_case = succ zero
    (.const hZero []))         -- b = zero
    (.app (.app (.const hEqRefl []) (.const hNat [])) (.const hZero []))  -- h = Eq.refl Nat zero

#eval GenericKernel.whnf env8 eqRecTest
-- should be: succ zero = App (Const hSucc) (Const hZero)

-- Test defEq via Eq.rec
def one := Expr.app (.const hSucc []) (.const hZero [])
#eval GenericKernel.defEq env8 eqRecTest one
-- should be: true

-- === Nat.add_zero : ∀ (n : Nat), Eq Nat (add n 0) n ===

def addZeroType : Expr :=
  .forallE (.const hNat [])
    (mkEq (mkAdd (.bvar 0) (.const hZero [])) (.bvar 0))
def hAddZero : UInt64 := (hashExpr addZeroType).1

def addZeroMotive : Expr :=
  .lam (.const hNat [])
    (mkEq (mkAdd (.bvar 0) (.const hZero [])) (.bvar 0))

def addZeroBase : Expr := mkRefl (.const hZero [])

def addZeroStep : Expr :=
  .lam (.const hNat [])
    (.lam (mkEq (mkAdd (.bvar 0) (.const hZero [])) (.bvar 0))
      (mkEqRec
        (mkAdd (.bvar 1) (.const hZero []))
        (.lam (.const hNat [])
          (mkEq (mkSucc' (mkAdd (.bvar 2) (.const hZero [])))
                (mkSucc' (.bvar 0))))
        (mkRefl (mkSucc' (mkAdd (.bvar 1) (.const hZero []))))
        (.bvar 1)
        (.bvar 0)))

def addZeroProof : Expr :=
  .lam (.const hNat [])
    (.app (.app (.app (.app (.const hRec [.zero]) addZeroMotive) addZeroBase) addZeroStep) (.bvar 0))

def env9 := (check hAddZero addZeroType (some addZeroProof) .definition env8).get!
#eval env9.size  -- should increase

-- === Nat.add_succ : ∀ (n m : Nat), Eq Nat (add n (succ m)) (succ (add n m)) ===

-- Verify definitional equality
#eval GenericKernel.defEq env9
  (mkAdd (.bvar 1) (mkSucc' (.bvar 0)))
  (mkSucc' (mkAdd (.bvar 1) (.bvar 0)))
  [.const hNat [], .const hNat []]

-- Type
def addSuccType : Expr :=
  .forallE (.const hNat [])
    (.forallE (.const hNat [])
      (mkEq (mkAdd (.bvar 1) (mkSucc' (.bvar 0)))
            (mkSucc' (mkAdd (.bvar 1) (.bvar 0)))))
def hAddSucc : UInt64 := (hashExpr addSuccType).1

-- Proof: fun n m => Eq.refl Nat (add n (succ m))
def addSuccProof : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (mkRefl (mkAdd (.bvar 1) (mkSucc' (.bvar 0)))))

-- CHECK
def env10 := (check hAddSucc addSuccType (some addSuccProof) .definition env9).get!
#eval env10.size

-- === zero_add : ∀ (n : Nat), Eq Nat (add zero n) n ===

def zeroAddType : Expr :=
  .forallE (.const hNat [])
    (mkEq (mkAdd (.const hZero []) (.bvar 0)) (.bvar 0))
def hZeroAdd : UInt64 := (hashExpr zeroAddType).1

def zeroAddMotive : Expr :=
  .lam (.const hNat [])
    (mkEq (mkAdd (.const hZero []) (.bvar 0)) (.bvar 0))

def zeroAddBase : Expr := mkRefl (.const hZero [])

def zeroAddStep : Expr :=
  .lam (.const hNat [])
    (.lam (mkEq (mkAdd (.const hZero []) (.bvar 0)) (.bvar 0))
      (mkEqRec
        (mkAdd (.const hZero []) (.bvar 1))
        (.lam (.const hNat [])
          (mkEq (mkSucc' (mkAdd (.const hZero []) (.bvar 2)))
                (mkSucc' (.bvar 0))))
        (mkRefl (mkSucc' (mkAdd (.const hZero []) (.bvar 1))))
        (.bvar 1)
        (.bvar 0)))

def zeroAddProof : Expr :=
  .lam (.const hNat [])
    (.app (.app (.app (.app (.const hRec [.zero]) zeroAddMotive) zeroAddBase) zeroAddStep) (.bvar 0))

def env11 := (check hZeroAdd zeroAddType (some zeroAddProof) .definition env10).get!
#eval env11.size

-- === succ_add : ∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m)) ===

def succAddType : Expr :=
  .forallE (.const hNat [])
    (.forallE (.const hNat [])
      (mkEq (mkAdd (mkSucc' (.bvar 1)) (.bvar 0))
            (mkSucc' (mkAdd (.bvar 1) (.bvar 0)))))
def hSuccAdd : UInt64 := (hashExpr succAddType).1

-- Proof: fun n m => Nat.rec [.zero] motive base step m
def succAddProof : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.app (.app (.app (.app (.const hRec [.zero])
        (.lam (.const hNat [])
          (mkEq (mkAdd (mkSucc' (.bvar 2)) (.bvar 0))
                (mkSucc' (mkAdd (.bvar 2) (.bvar 0))))))
        (mkRefl (mkAdd (mkSucc' (.bvar 1)) (.const hZero []))))
        (.lam (.const hNat [])
          (.lam (mkEq (mkAdd (mkSucc' (.bvar 2)) (.bvar 0))
                      (mkSucc' (mkAdd (.bvar 2) (.bvar 0))))
            (mkEqRec
              (mkAdd (mkSucc' (.bvar 3)) (.bvar 1))
              (.lam (.const hNat [])
                (mkEq (mkSucc' (mkAdd (mkSucc' (.bvar 4)) (.bvar 2)))
                      (mkSucc' (.bvar 0))))
              (mkRefl (mkSucc' (mkAdd (mkSucc' (.bvar 3)) (.bvar 1))))
              (mkSucc' (mkAdd (.bvar 3) (.bvar 1)))
              (.bvar 0)))))
        (.bvar 0)))

def env12 := (check hSuccAdd succAddType (some succAddProof) .definition env11).get!
#eval env12.size

-- === Eq.symm : ∀ (a b : Nat), Eq Nat a b -> Eq Nat b a ===

def eqSymmType : Expr :=
  .forallE (.const hNat [])
    (.forallE (.const hNat [])
      (.forallE (mkEq (.bvar 1) (.bvar 0))
        (mkEq (.bvar 1) (.bvar 2))))
def hEqSymm : UInt64 := (hashExpr eqSymmType).1

def eqSymmProof : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.lam (mkEq (.bvar 1) (.bvar 0))
        (mkEqRec
          (.bvar 2)
          (.lam (.const hNat [])
            (mkEq (.bvar 0) (.bvar 3)))
          (mkRefl (.bvar 2))
          (.bvar 1)
          (.bvar 0))))

def env13 := (check hEqSymm eqSymmType (some eqSymmProof) .definition env12).get!
#eval env13.size

-- === Eq.trans : ∀ (a b c : Nat), Eq Nat a b -> Eq Nat b c -> Eq Nat a c ===

def eqTransType : Expr :=
  .forallE (.const hNat [])
    (.forallE (.const hNat [])
      (.forallE (.const hNat [])
        (.forallE (mkEq (.bvar 2) (.bvar 1))
          (.forallE (mkEq (.bvar 2) (.bvar 1))
            (mkEq (.bvar 4) (.bvar 2))))))
def hEqTrans : UInt64 := (hashExpr eqTransType).1

def eqTransProof : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.lam (.const hNat [])
        (.lam (mkEq (.bvar 2) (.bvar 1))
          (.lam (mkEq (.bvar 2) (.bvar 1))
            (mkEqRec
              (.bvar 3)
              (.lam (.const hNat [])
                (mkEq (.bvar 5) (.bvar 0)))
              (.bvar 1)
              (.bvar 2)
              (.bvar 0))))))

def env14 := (check hEqTrans eqTransType (some eqTransProof) .definition env13).get!
#eval env14.size

-- === Nat.add_comm : ∀ (n m : Nat), Eq Nat (add n m) (add m n) ===

def addCommType : Expr :=
  .forallE (.const hNat [])
    (.forallE (.const hNat [])
      (mkEq (mkAdd (.bvar 1) (.bvar 0)) (mkAdd (.bvar 0) (.bvar 1))))
def hAddComm : UInt64 := (hashExpr addCommType).1

def addCommMotive : Expr :=
  .lam (.const hNat [])
    (mkEq (mkAdd (.bvar 0) (.bvar 1)) (mkAdd (.bvar 1) (.bvar 0)))

-- base: under [n, m]: m=BVar0
def addCommBase : Expr :=
  let m := Expr.bvar 0
  let zero := Expr.const hZero []
  let zam := Expr.app (.const hZeroAdd []) m
  let azm := Expr.app (.const hAddZero []) m
  let sym_azm := Expr.app (.app (.app (.const hEqSymm []) (mkAdd m zero)) m) azm
  .app (.app (.app (.app (.app (.const hEqTrans [])
    (mkAdd zero m))
    m)
    (mkAdd m zero))
    zam)
    sym_azm

-- step: under [n, m, k, ih]: ih=BVar0, k=BVar1, m=BVar2, n=BVar3
def addCommStep : Expr :=
  .lam (.const hNat [])
    (.lam (mkEq (mkAdd (.bvar 0) (.bvar 1)) (mkAdd (.bvar 1) (.bvar 0)))
      (let k := Expr.bvar 1
       let m := Expr.bvar 2
       let ih := Expr.bvar 0
       let sa := Expr.app (.app (.const hSuccAdd []) k) m
       let cong :=
         mkEqRec
           (mkAdd k m)
           (.lam (.const hNat [])
             (mkEq (mkSucc' (mkAdd (.bvar 2) (.bvar 3)))
                   (mkSucc' (.bvar 0))))
           (mkRefl (mkSucc' (mkAdd k m)))
           (mkAdd m k)
           ih
       let as_mk := Expr.app (.app (.const hAddSucc []) m) k
       let sym_as := Expr.app (.app (.app (.const hEqSymm [])
         (mkAdd m (mkSucc' k)))
         (mkSucc' (mkAdd m k)))
         as_mk
       let inner_trans := Expr.app (.app (.app (.app (.app (.const hEqTrans [])
         (mkSucc' (mkAdd k m)))
         (mkSucc' (mkAdd m k)))
         (mkAdd m (mkSucc' k)))
         cong)
         sym_as
       Expr.app (.app (.app (.app (.app (.const hEqTrans [])
         (mkAdd (mkSucc' k) m))
         (mkSucc' (mkAdd k m)))
         (mkAdd m (mkSucc' k)))
         sa)
         inner_trans))

def addCommProof : Expr :=
  .lam (.const hNat [])
    (.lam (.const hNat [])
      (.app (.app (.app (.app (.const hRec [.zero]) addCommMotive) addCommBase) addCommStep) (.bvar 1)))

def env15 := (check hAddComm addCommType (some addCommProof) .definition env14).get!
#eval env15.size

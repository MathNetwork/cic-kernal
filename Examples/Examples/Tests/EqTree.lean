import Examples.Setup.TreeSetup
open TreeKernel

-- === Tests ===

-- Check env sizes
#eval env6.size  -- 6
#eval env7.size  -- 7
#eval env8.size  -- 8

-- Infer Eq.refl type
#eval infer env8 (.const "Eq.refl" [])

-- Construct: Eq.refl Nat Nat.zero  (proof that zero = zero)
-- This should have type: Eq Nat Nat.zero Nat.zero
def reflZero : Expr := .app (.app (.const "Eq.refl" []) (.const "Nat" [])) (.const "Nat.zero" [])
#eval infer env8 reflZero

-- === Nat.add_zero : ∀ (n : Nat), Eq Nat (add n 0) n ===

-- Type: ∀ (n : Nat), Eq Nat (add n 0) n
def addZeroType : Expr :=
  .forallE (.const "Nat" [])
    (mkEq (mkAdd (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))

-- motive: fun (k : Nat) => Eq Nat (add k 0) k
def addZeroMotive : Expr :=
  .lam (.const "Nat" [])  -- k : Nat
    (mkEq (mkAdd (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))

-- base: Eq.refl Nat zero
def addZeroBase : Expr := mkRefl (.const "Nat.zero" [])

-- step: fun (k : Nat) (ih : Eq Nat (add k 0) k) =>
--   Eq.rec Nat (add k 0)
--     (fun (x : Nat) => Eq Nat (succ (add k 0)) (succ x))
--     (Eq.refl Nat (succ (add k 0)))
--     k ih
def addZeroStep : Expr :=
  .lam (.const "Nat" [])                                      -- k : Nat
    (.lam (mkEq (mkAdd (.bvar 0) (.const "Nat.zero" [])) (.bvar 0))  -- ih : Eq Nat (add k 0) k
      -- body: Eq.rec Nat (add k 0) motive' reflCase k ih
      -- k = BVar 1, ih = BVar 0
      (mkEqRec
        (mkAdd (.bvar 1) (.const "Nat.zero" []))               -- a = add k 0
        (.lam (.const "Nat" [])                                 -- motive' = fun (x : Nat) =>
          (mkEq (mkSucc (mkAdd (.bvar 2) (.const "Nat.zero" [])))  -- Eq Nat (succ (add k 0))
                (mkSucc (.bvar 0))))                            --        (succ x)
          -- x = BVar 0, k = BVar 2 (skip ih and x)
        (mkRefl (mkSucc (mkAdd (.bvar 1) (.const "Nat.zero" []))))  -- Eq.refl Nat (succ (add k 0))
        (.bvar 1)                                            -- b = k
        (.bvar 0)))                                          -- h = ih

-- Full proof: fun (n : Nat) => Nat.rec [.zero] motive base step n
def addZeroProof : Expr :=
  .lam (.const "Nat" [])
    (.app (.app (.app (.app (.const "Nat.rec" [.zero]) addZeroMotive) addZeroBase) addZeroStep) (.bvar 0))

-- Debug: check components
#eval infer env8 addZeroMotive   -- should be ForallE Nat (Sort 0) or similar
#eval infer env8 addZeroBase     -- should be Eq Nat zero zero

-- Debug: infer the full proof
#eval infer env8 addZeroProof

-- Debug: infer just the step
#eval infer env8 addZeroStep

-- Debug: infer Nat.rec applied to motive only
#eval infer env8 (.app (.const "Nat.rec" [.zero]) addZeroMotive)

-- THE CHECK
def env9 := (check "Nat.add_zero" addZeroType (some addZeroProof) .definition env8).get!
#eval env9.size  -- 9

-- === Nat.add_succ : ∀ (n m : Nat), Eq Nat (add n (succ m)) (succ (add n m)) ===

-- Verify: add n (succ m) is definitionally equal to succ (add n m)
#eval defEq env9
  (mkAdd (.bvar 1) (mkSucc (.bvar 0)))
  (mkSucc (mkAdd (.bvar 1) (.bvar 0)))
  [.const "Nat" [], .const "Nat" []]

-- Type
def addSuccType : Expr :=
  .forallE (.const "Nat" [])
    (.forallE (.const "Nat" [])
      (mkEq (mkAdd (.bvar 1) (mkSucc (.bvar 0)))
            (mkSucc (mkAdd (.bvar 1) (.bvar 0)))))

-- Proof: fun n m => Eq.refl Nat (add n (succ m))
-- Works because add n (succ m) definitionally equals succ (add n m)
def addSuccProof : Expr :=
  .lam (.const "Nat" [])
    (.lam (.const "Nat" [])
      (mkRefl (mkAdd (.bvar 1) (mkSucc (.bvar 0)))))

-- CHECK
def env10 := (check "Nat.add_succ" addSuccType (some addSuccProof) .definition env9).get!
#eval env10.size

-- === zero_add : ∀ (n : Nat), Eq Nat (add zero n) n ===

def zeroAddType : Expr :=
  .forallE (.const "Nat" [])
    (mkEq (mkAdd (.const "Nat.zero" []) (.bvar 0)) (.bvar 0))

def zeroAddMotive : Expr :=
  .lam (.const "Nat" [])
    (mkEq (mkAdd (.const "Nat.zero" []) (.bvar 0)) (.bvar 0))

def zeroAddBase : Expr := mkRefl (.const "Nat.zero" [])

-- step: fun (k : Nat) (ih : Eq Nat (add zero k) k) =>
--   Eq.rec Nat (add zero k)
--     (fun x => Eq Nat (succ (add zero k)) (succ x))
--     (Eq.refl Nat (succ (add zero k)))
--     k ih
def zeroAddStep : Expr :=
  .lam (.const "Nat" [])
    (.lam (mkEq (mkAdd (.const "Nat.zero" []) (.bvar 0)) (.bvar 0))
      (mkEqRec
        (mkAdd (.const "Nat.zero" []) (.bvar 1))
        (.lam (.const "Nat" [])
          (mkEq (mkSucc (mkAdd (.const "Nat.zero" []) (.bvar 2)))
                (mkSucc (.bvar 0))))
        (mkRefl (mkSucc (mkAdd (.const "Nat.zero" []) (.bvar 1))))
        (.bvar 1)
        (.bvar 0)))

def zeroAddProof : Expr :=
  .lam (.const "Nat" [])
    (.app (.app (.app (.app (.const "Nat.rec" [.zero]) zeroAddMotive) zeroAddBase) zeroAddStep) (.bvar 0))

def env11 := (check "zero_add" zeroAddType (some zeroAddProof) .definition env10).get!
#eval env11.size

-- === succ_add : ∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m)) ===

def succAddType : Expr :=
  .forallE (.const "Nat" [])
    (.forallE (.const "Nat" [])
      (mkEq (mkAdd (mkSucc (.bvar 1)) (.bvar 0))
            (mkSucc (mkAdd (.bvar 1) (.bvar 0)))))

-- Proof: fun n m => Nat.rec [.zero] motive base step m
def succAddProof : Expr :=
  .lam (.const "Nat" [])
    (.lam (.const "Nat" [])
      (.app (.app (.app (.app (.const "Nat.rec" [.zero])
        (.lam (.const "Nat" [])
          (mkEq (mkAdd (mkSucc (.bvar 2)) (.bvar 0))
                (mkSucc (mkAdd (.bvar 2) (.bvar 0))))))
        (mkRefl (mkAdd (mkSucc (.bvar 1)) (.const "Nat.zero" []))))
        (.lam (.const "Nat" [])
          (.lam (mkEq (mkAdd (mkSucc (.bvar 2)) (.bvar 0))
                      (mkSucc (mkAdd (.bvar 2) (.bvar 0))))
            (mkEqRec
              (mkAdd (mkSucc (.bvar 3)) (.bvar 1))
              (.lam (.const "Nat" [])
                (mkEq (mkSucc (mkAdd (mkSucc (.bvar 4)) (.bvar 2)))
                      (mkSucc (.bvar 0))))
              (mkRefl (mkSucc (mkAdd (mkSucc (.bvar 3)) (.bvar 1))))
              (mkSucc (mkAdd (.bvar 3) (.bvar 1)))
              (.bvar 0)))))
        (.bvar 0)))

def env12 := (check "succ_add" succAddType (some succAddProof) .definition env11).get!
#eval env12.size

-- === Eq.symm : ∀ (a b : Nat), Eq Nat a b -> Eq Nat b a ===

def eqSymmType : Expr :=
  .forallE (.const "Nat" [])
    (.forallE (.const "Nat" [])
      (.forallE (mkEq (.bvar 1) (.bvar 0))
        (mkEq (.bvar 1) (.bvar 2))))

def eqSymmProof : Expr :=
  .lam (.const "Nat" [])                              -- a
    (.lam (.const "Nat" [])                            -- b; a=BVar1
      (.lam (mkEq (.bvar 1) (.bvar 0))                -- h; a=BVar2, b=BVar1
        (mkEqRec
          (.bvar 2)                                    -- a
          (.lam (.const "Nat" [])                      -- fun x; a=BVar3, b=BVar2, h=BVar1, x=BVar0
            (mkEq (.bvar 0) (.bvar 3)))                -- Eq Nat x a
          (mkRefl (.bvar 2))                           -- Eq.refl Nat a; a=BVar2
          (.bvar 1)                                    -- b
          (.bvar 0))))                                 -- h

def env13 := (check "Eq.symm" eqSymmType (some eqSymmProof) .definition env12).get!
#eval env13.size

-- === Eq.trans : ∀ (a b c : Nat), Eq Nat a b -> Eq Nat b c -> Eq Nat a c ===

def eqTransType : Expr :=
  .forallE (.const "Nat" [])                                    -- a
    (.forallE (.const "Nat" [])                                  -- b
      (.forallE (.const "Nat" [])                                -- c; a=BVar2, b=BVar1, c=BVar0
        (.forallE (mkEq (.bvar 2) (.bvar 1))                    -- hab; a=BVar3, b=BVar2, c=BVar1
          (.forallE (mkEq (.bvar 2) (.bvar 1))                  -- hbc; a=BVar4, b=BVar3, c=BVar2
            (mkEq (.bvar 4) (.bvar 2))))))                      -- Eq Nat a c

def eqTransProof : Expr :=
  .lam (.const "Nat" [])                                        -- a
    (.lam (.const "Nat" [])                                      -- b
      (.lam (.const "Nat" [])                                    -- c; a=BVar2, b=BVar1, c=BVar0
        (.lam (mkEq (.bvar 2) (.bvar 1))                        -- hab; a=BVar3, b=BVar2, c=BVar1
          (.lam (mkEq (.bvar 2) (.bvar 1))                      -- hbc; a=BVar4, b=BVar3, c=BVar2
            (mkEqRec                                             -- Under [a,b,c,hab,hbc]: 4=a,3=b,2=c,1=hab,0=hbc
              (.bvar 3)                                          -- Eq.rec's a = b
              (.lam (.const "Nat" [])                            -- fun x; a=BVar5, x=BVar0
                (mkEq (.bvar 5) (.bvar 0)))                     -- Eq Nat a x
              (.bvar 1)                                          -- refl_case = hab : Eq Nat a b
              (.bvar 2)                                          -- target = c
              (.bvar 0))))))                                     -- h = hbc : Eq Nat b c

def env14 := (check "Eq.trans" eqTransType (some eqTransProof) .definition env13).get!
#eval env14.size

-- === Nat.add_comm : ∀ (n m : Nat), Eq Nat (add n m) (add m n) ===

def addCommType : Expr :=
  .forallE (.const "Nat" [])
    (.forallE (.const "Nat" [])
      (mkEq (mkAdd (.bvar 1) (.bvar 0)) (mkAdd (.bvar 0) (.bvar 1))))

-- Proof by induction on n: fun n m => Nat.rec motive base step n
-- Under fun n m: n=BVar1, m=BVar0

-- motive: fun k => Eq Nat (add k m) (add m k)
-- Under [n, m, k]: k=BVar0, m=BVar1
def addCommMotive : Expr :=
  .lam (.const "Nat" [])
    (mkEq (mkAdd (.bvar 0) (.bvar 1)) (mkAdd (.bvar 1) (.bvar 0)))

-- base: Eq Nat (add 0 m) (add m 0)
-- = Eq.trans (add 0 m) m (add m 0) (zero_add m) (Eq.symm (add m 0) m (add_zero m))
-- Under [n, m]: m=BVar0
def addCommBase : Expr :=
  let m := Expr.bvar 0
  let zero := Expr.const "Nat.zero" []
  -- zero_add m : Eq (add 0 m) m
  let zam := Expr.app (.const "zero_add" []) m
  -- add_zero m : Eq (add m 0) m
  let azm := Expr.app (.const "Nat.add_zero" []) m
  -- Eq.symm (add m 0) m (add_zero m) : Eq m (add m 0)
  let sym_azm := Expr.app (.app (.app (.const "Eq.symm" []) (mkAdd m zero)) m) azm
  -- Eq.trans (add 0 m) m (add m 0) zam sym_azm
  .app (.app (.app (.app (.app (.const "Eq.trans" [])
    (mkAdd zero m))    -- a = add 0 m
    m)                 -- b = m
    (mkAdd m zero))    -- c = add m 0
    zam)               -- hab = zero_add m
    sym_azm            -- hbc = Eq.symm ... (add_zero m)

-- step: fun k ih => ... prove Eq Nat (add (succ k) m) (add m (succ k))
-- Chain: succ_add k m, then cong_succ ih, then Eq.symm (add_succ m k)
-- Under [n, m, k, ih]: ih=BVar0, k=BVar1, m=BVar2, n=BVar3
def addCommStep : Expr :=
  .lam (.const "Nat" [])                                          -- k
    (.lam (mkEq (mkAdd (.bvar 0) (.bvar 1)) (mkAdd (.bvar 1) (.bvar 0)))  -- ih; k=BVar1, m=BVar2
      -- Now under [n, m, k, ih]: ih=BVar0, k=BVar1, m=BVar2, n=BVar3
      (let k := Expr.bvar 1
       let m := Expr.bvar 2
       let ih := Expr.bvar 0
       -- 1. succ_add k m : Eq (add (succ k) m) (succ (add k m))
       let sa := Expr.app (.app (.const "succ_add" []) k) m
       -- 2. cong_succ: Eq (succ (add k m)) (succ (add m k)) via Eq.rec on ih
       let cong :=
         mkEqRec
           (mkAdd k m)                                            -- a = add k m
           (.lam (.const "Nat" [])                                -- fun x; k=BVar2, m=BVar3, x=BVar0
             (mkEq (mkSucc (mkAdd (.bvar 2) (.bvar 3)))          -- succ (add k m)
                   (mkSucc (.bvar 0))))                           -- succ x
           (mkRefl (mkSucc (mkAdd k m)))                          -- Eq.refl (succ (add k m))
           (mkAdd m k)                                            -- b = add m k
           ih                                                     -- h = ih
       -- 3. Eq.symm on add_succ m k
       -- add_succ m k : Eq (add m (succ k)) (succ (add m k))
       let as_mk := Expr.app (.app (.const "Nat.add_succ" []) m) k
       -- Eq.symm (add m (succ k)) (succ (add m k)) (add_succ m k) : Eq (succ (add m k)) (add m (succ k))
       let sym_as := Expr.app (.app (.app (.const "Eq.symm" [])
         (mkAdd m (mkSucc k)))                                    -- a = add m (succ k)
         (mkSucc (mkAdd m k)))                                    -- b = succ (add m k)
         as_mk
       -- inner_trans: Eq (succ (add k m)) (add m (succ k))
       let inner_trans := Expr.app (.app (.app (.app (.app (.const "Eq.trans" [])
         (mkSucc (mkAdd k m)))                                    -- a = succ (add k m)
         (mkSucc (mkAdd m k)))                                    -- b = succ (add m k)
         (mkAdd m (mkSucc k)))                                    -- c = add m (succ k)
         cong)
         sym_as
       -- outer_trans: Eq (add (succ k) m) (add m (succ k))
       Expr.app (.app (.app (.app (.app (.const "Eq.trans" [])
         (mkAdd (mkSucc k) m))                                    -- a = add (succ k) m
         (mkSucc (mkAdd k m)))                                    -- b = succ (add k m)
         (mkAdd m (mkSucc k)))                                    -- c = add m (succ k)
         sa)
         inner_trans))

-- Full proof: fun n m => Nat.rec [.zero] motive base step n
def addCommProof : Expr :=
  .lam (.const "Nat" [])
    (.lam (.const "Nat" [])
      (.app (.app (.app (.app (.const "Nat.rec" [.zero]) addCommMotive) addCommBase) addCommStep) (.bvar 1)))

def env15 := (check "Nat.add_comm" addCommType (some addCommProof) .definition env14).get!
#eval env15.size

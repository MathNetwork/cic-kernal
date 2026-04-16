import HypergraphKernel.Defs

open HypergraphKernel

instance : HasBuiltinKeys UInt64 where
  natKey := "Sort(Ls(L0))".hash
  stringKey := "Sort(Ls(L0))".hash

partial def defEq (env : Env UInt64) (a b : Expr) (ctx : List Expr := []) : Bool :=
  GenericKernel.defEq env a b ctx

def «infer» (env : Env UInt64) (e : Expr) (ctx : List Expr := []) : Option Expr :=
  GenericKernel.infer env e ctx

def «whnf» (env : Env UInt64) (e : Expr) : Expr :=
  GenericKernel.whnf env e

def check (h : UInt64) (T : Expr) (v : Option Expr) (kind : DeclKind) (env : Env UInt64) : Option (Env UInt64) :=
  GenericKernel.check h T v kind env

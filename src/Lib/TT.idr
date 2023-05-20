module Lib.TT
-- For SourcePos
import Lib.Parser.Impl

public export
Name : Type
Name = String

export
data Icit = Implicit | Explicit

-- Sorta cribbed from Kovacs
Ty : Type

-- Idris and Kovacs have Icit at this level.
public export
data Tm
  = Local Nat -- IsVar
  | Ref String
  | Lam Name Icit Tm
  | App Tm Tm
  | U
  | Pi Name Ty Ty
  | Let Name Ty Tm Tm
  
Ty = Tm

public export
data Closure : Type
VTy : Type

 -- Closure unpacked in the original
public export
data Val
  = VVar Nat -- level
  | VApp Val (Lazy Val)
  | VLam Name Icit Closure
  | VPi Name (Lazy VTy) Closure
  | VU

VTy = Val

public export
Env : Type
Env = List Val

-- 

lvl2Ix : Nat -> Nat -> Nat

data Closure : Type where
  MkClosure :  Env -> Tm -> Closure

infixl 8 $$

eval : Env -> Tm -> Val

($$) : Closure -> Lazy Val -> Val
(MkClosure env t) $$ u = eval (u :: env) t

eval env (Local k) = ?hole
eval env (Ref x) = ?hole_1
eval env (Lam x _ t) = ?hole_2
eval env (App t u) = case (eval env t, eval env u) of
  (VLam _ icit t, u) => t $$ u
  (t, u) => VApp t u

eval env U = VU
eval env (Pi x a b) = VPi x (eval env a) (MkClosure env b)
eval env (Let x _ t u) = eval (eval env t :: env) u

quote : Nat -> Val -> Tm
quote l (VVar k) = Local (lvl2Ix l k)
quote l (VApp t u) = App (quote l t) (quote l u)
quote l (VLam x icit t) = Lam x icit (quote (l + 1) (t $$ VVar l))
quote l (VPi x a b) = Pi x (quote l a) (quote (l+1) (b $$ VVar l))
quote l VU = ?rhs_4

nf : Env -> Tm -> Tm
nf env t = quote (length env) (eval env t)

---
public export
conv : (lvl : Nat) -> Val -> Val -> Bool


-- 
public export
Types : Type
Types = List (Name, Lazy VTy)

public export
record Ctx where
  constructor MkCtx
  env : Env
  types : Types
  lvl : Nat
  -- For now, we're following Kovacs and using a node for
  -- source position. Might switch to FC at some point?
  pos : SourcePos

public export
emptyCtx : Ctx
emptyCtx = MkCtx [] [] 0 (0,0)

public export
bind : Name -> Lazy VTy -> Ctx -> Ctx
bind x a (MkCtx env types l pos) =
  MkCtx (VVar l :: env) ((x,a) :: types) (l+1) pos



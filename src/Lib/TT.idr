module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Data.Fin
import Data.Vect

public export
Name : Type
Name = String

-- Trying to do well-scoped here, so the indices are proven.

export
data Icit = Implicit | Explicit

%name Icit icit

public export
data Tm : Nat -> Nat -> Type where
  Local : Fin k -> Tm k n
  Bnd : Fin n -> Tm k n
  Ref   : String -> Tm k n
  Lam   : Name -> Icit -> Tm k (S n) -> Tm k n
  App   : Tm k n -> Tm k n -> Tm k n
  U     : Tm k n
  Pi    : Name -> Icit -> Tm k n -> Tm k (S n) -> Tm k n
  Let   : Name -> Icit -> Tm k n -> Tm k n -> Tm k (S n) -> Tm k n

%name Tm t, u, v

-- public export
-- data Closure : Nat -> Type
data Val : Nat -> Type
0 Closure : Nat -> Type

-- IS/TypeTheory.idr is calling this a Kripke function space
-- Yaffle, IS/TypeTheory use a function here.
-- Kovacs, Idris use Env and Tm
Closure n = (l : Nat) -> Val (l + n) -> Val (l + n)

public export
data Val : Nat -> Type where
  -- This will be local / flex with spine.
  VVar : Fin n -> Val n
  VRef : String -> Val n
  VApp : Val n ->  Lazy (Val n) -> Val n
  VLam : Name -> Icit -> Closure n -> Val n
  VPi : Name -> Icit -> Lazy (Val n) -> Closure n -> Val n
  VU : Val n

||| Env k n holds the evaluation environment.
||| k is the number of levels and n is the size
||| of the environment. 
public export
Env : Nat -> Nat -> Type
Env k n = Vect n (Val k)

export
eval : Env k n -> Tm k n -> Val k

vapp : Val k -> Val k -> Val k
vapp (VLam _ icit t) u = t 0 u
vapp t u = VApp t u

-- weakenEnv : (l : Nat) -> Env k n -> Env (l + k) n

weakenVal : {e : Nat} -> Val k -> Val (e + k)
weakenVal (VVar x) = VVar (shift _ x)
weakenVal (VRef str) = VRef str
weakenVal (VApp x y) = VApp (weakenVal x) (weakenVal y)
weakenVal (VLam str icit f) = VLam str icit 
      (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
weakenVal (VPi str icit x f) = VPi str icit (weakenVal {e} x) 
      (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
weakenVal VU = VU

bind : (e : Nat) -> Val (plus e k) -> Env k n -> Env (e + k) (S n)
bind e v env = v :: map weakenVal env

-- is this weaken or thin?
weaken : {e : Nat} -> Tm k (S n) -> Tm (plus e k) (S n)
weaken (Local x) = Local (shift _ x)
weaken (Bnd x) = Bnd x
weaken (Ref str) = Ref str
weaken (Lam str x t) = Lam str x (weaken t)
weaken (App t u) = App (weaken t) (weaken u)
weaken U = U
weaken (Pi str x t u) = Pi str x (weaken t) (weaken u)
weaken (Let str x t u v) = Let str x (weaken t) (weaken u) (weaken v)

eval env (Local x) = VVar x -- this is a hole in intrinsic, vfree x in the other 
eval env (Ref x) = VRef x
eval env (Bnd n) = index n env
eval env (Lam x icit t) = VLam x icit (\e, u => eval (bind e u env) (weaken t))-- (MkClosure env t) 
eval env (App t u) = vapp (eval env t) (eval env u)
eval env U = VU
eval env (Pi x icit a b) = VPi x icit (eval env a) (\e, u => eval (bind e u env) (weaken b))
-- This one we need to make 
eval env (Let x icit ty t u) = eval (eval env t :: env) u

vfresh : (l : Nat) -> Val (S l)
vfresh l = VVar last

quote : (k : Nat) -> Val k -> Tm 0 k
quote l (VVar k) = Bnd (complement k) -- level to index
quote l (VApp t u) = App (quote l t) (quote l u)
-- so this one is calling the kripke on [x] and a fresh var
quote l (VLam x icit t) = Lam x icit (quote (S l) (t 1 (vfresh l)))
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (b 1 $ vfresh l))
quote l VU = U
quote _ (VRef n) = Ref n

nf : {n : Nat} -> Env 0 n -> Tm 0 n -> Tm 0 0
nf env t = quote 0 (eval env t)

public export
conv : (lvl : Nat) -> Val n -> Val n -> Bool

data BD = Bound | Defined

public export
Types : Nat -> Type
Types n = Vect n (Name, Lazy (Val n))

public export
record Ctx (n : Nat) where
  constructor MkCtx
  env : Env k n     -- for eval
  types : Types n   -- name lookup, pp
  bds : Vect n BD  -- meta creation
  lvl : Nat -- This is n, do we need it?
  -- Kovacs and Weirich use a position node
  pos : SourcePos

%name Ctx ctx

public export
emptyCtx : Ctx Z
emptyCtx = MkCtx {k=0} [] [] [] 0 (0,0)

-- public export
-- bind : Name -> Lazy (Val (k + n))  -> Ctx n -> Ctx (S n)
-- bind x a (MkCtx env types bds l pos) =
--   MkCtx (VVar l :: env) ((x,a) :: types) (Bound :: bds) (l+1) pos

-- public export
-- define : Name -> Val n -> Lazy (Val n)  -> Ctx n -> Ctx (S n)
-- define x v ty (MkCtx env types bds l pos) =
--   MkCtx (v :: env) ((x,ty) :: types) (Defined :: bds) (l + 1) pos


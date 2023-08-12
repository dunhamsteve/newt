module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Data.Fin
import Data.Vect

public export
Name : Type
Name = String

-- Trying to do well-scoped here, so the indices are proven.

public export
data Icit = Implicit | Explicit

%name Icit icit

public export
data Tm : Nat -> Type where
  Bnd : Fin n -> Tm n
  Ref : String -> Tm n
  Lam : Name -> Icit -> Tm (S n) -> Tm n
  App : Tm n -> Tm n -> Tm n
  U   : Tm n
  Pi  : Name -> Icit -> Tm n -> Tm (S n) -> Tm n
  Let : Name -> Icit -> Tm n -> Tm n -> Tm (S n) -> Tm n

%name Tm t, u, v

-- TODO derive
export
Eq (Tm n) where
  -- (Local x) == (Local y) = x == y
  (Bnd x) == (Bnd y) = x == y
  (Ref x) == (Ref y) = x == y
  (Lam str icit t) == y = ?rhs_3
  (App t u) == y = ?rhs_4
  U == y = ?rhs_5
  (Pi str icit t u) == y = ?rhs_6
  (Let str icit t u v) == y = ?rhs_7
  _ == _ = False

-- public export
-- data Closure : Nat -> Type
data Val : Nat -> Type

public export
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
eval : Env k n -> Tm n -> Val k

export
vapp : Val k -> Val k -> Val k
vapp (VLam _ icit t) u = t 0 u
vapp t u = VApp t u

-- thinEnv : (l : Nat) -> Env k n -> Env (l + k) n

thinVal : {e : Nat} -> Val k -> Val (e + k)
thinVal (VVar x) = VVar (shift _ x)
thinVal (VRef str) = VRef str
thinVal (VApp x y) = VApp (thinVal x) (thinVal y)
thinVal (VLam str icit f) = VLam str icit 
      (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
thinVal (VPi str icit x f) = VPi str icit (thinVal {e} x) 
      (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
thinVal VU = VU

bind : (e : Nat) -> Val (plus e k) -> Env k n -> Env (e + k) (S n)
bind e v env = v :: map thinVal env

eval env (Ref x) = VRef x
eval env (Bnd n) = index n env
eval env (Lam x icit t) = VLam x icit (\e, u => eval (bind e u env) t)-- (MkClosure env t) 
eval env (App t u) = vapp (eval env t) (eval env u)
eval env U = VU
eval env (Pi x icit a b) = VPi x icit (eval env a) (\e, u => eval (bind e u env) b)
-- This one we need to make 
eval env (Let x icit ty t u) = eval (eval env t :: env) u

vfresh : (l : Nat) -> Val (S l)
vfresh l = VVar last

export
quote : (k : Nat) -> Val k -> Tm k
quote l (VVar k) = Bnd (complement k) -- level to index
quote l (VApp t u) = App (quote l t) (quote l u)
-- so this one is calling the kripke on [x] and a fresh var
quote l (VLam x icit t) = Lam x icit (quote (S l) (t 1 (vfresh l)))
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (b 1 $ vfresh l))
quote l VU = U
quote _ (VRef n) = Ref n

export
nf : {n : Nat} -> Env 0 n -> Tm n -> Tm 0
nf env t = quote 0 (eval env t)

public export
conv : (lvl : Nat) -> Val n -> Val n -> Bool

data BD = Bound | Defined

public export
Types : Nat -> Type
Types n = Vect n (Name, Lazy (Val n))

-- public export
-- record Ctx (n : Nat) where
--   constructor MkCtx
--   env : Env k n     -- for eval
--   types : Types n   -- name lookup, pp
--   bds : Vect n BD  -- meta creation
--   lvl : Nat -- This is n, do we need it?
--   -- Kovacs and Weirich use a position node
--   pos : SourcePos

-- %name Ctx ctx

-- public export
-- emptyCtx : Ctx Z
-- emptyCtx = MkCtx {k=0} [] [] [] 0 (0,0)

-- public export
-- bindCtx : Name -> Lazy (Val (zz + n))  -> Ctx n -> Ctx (S n)
-- bindCtx x a (MkCtx env types bds l pos) =
--   MkCtx (VVar l :: env) ((x,a) :: map (map thinVal) types) (Bound :: bds) (l+1) pos

-- public export
-- define : Name -> Val n -> Lazy (Val n)  -> Ctx n -> Ctx (S n)
-- define x v ty (MkCtx env types bds l pos) =
--   MkCtx (v :: env) ((x,ty) :: map (map thinVal) types) (Defined :: bds) (l + 1) pos


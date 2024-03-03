-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

-- The Control.App requires a patched idris. :(

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Data.Fin
import Data.List

public export
Name : Type
Name = String

public export
data Icit = Implicit | Explicit

%name Icit icit

public export
data Tm : Type where
  Bnd : Nat -> Tm
  Ref : String -> Tm
  Lam : Name -> Icit -> Tm -> Tm
  App : Tm -> Tm -> Tm
  U   : Tm
  Pi  : Name -> Icit -> Tm -> Tm -> Tm
  Let : Name -> Icit -> Tm -> Tm -> Tm -> Tm

%name Tm t, u, v

-- TODO derive
export 
Eq Icit where
  Implicit == Implicit = True
  Explicit == Explicit = True
  _ == _ = False

||| Eq on Tm. We've got deBruijn indices, so I'm not comparing names
export
Eq (Tm) where
  -- (Local x) == (Local y) = x == y
  (Bnd x) == (Bnd y) = x == y
  (Ref x) == (Ref y) = x == y
  (Lam n icit t) == (Lam n' icit' t') = icit == icit' && t == t'
  (App t u) == App t' u' = t == t' && u == u'
  U == U = True
  (Pi n icit t u) == (Pi n' icit' t' u') = icit == icit' && t == t' && u == u'
  (Let n icit t u v) == (Let n' icit' t' u' v') = t == t' && u == u' && v == v'
  _ == _ = False

-- public export
-- data Closure : Nat -> Type
data Val : Type


-- IS/TypeTheory.idr is calling this a Kripke function space
-- Yaffle, IS/TypeTheory use a function here.
-- Kovacs, Idris use Env and Tm

-- in cctt kovacs refers to this choice as defunctionalization vs HOAS
-- https://github.com/AndrasKovacs/cctt/blob/main/README.md#defunctionalization
-- the tradeoff is access to internals of the function

-- Yaffle is vars -> vars here


public export
0 Closure : Type
Closure = Val -> Val

public export
data Val : Type where
  -- This will be local / flex with spine.
  VVar : Nat -> Val
  VRef : String -> Val
  VApp : Val ->  Lazy (Val) -> Val
  VLam : Name -> Icit -> Closure -> Val
  VPi : Name -> Icit -> Lazy Val -> Closure -> Val
  VU : Val

||| LocalEnv free vars
public export
LocalEnv : Type 
LocalEnv = List Val

public export
Env : Type
Env = List Val

export
eval : LocalEnv -> Env -> Tm -> Val

export
vapp : Val -> Val -> Val
vapp (VLam _ icit t) u = t u
vapp t u = VApp t u

bind : Val -> Env -> Env
bind v env = v :: env

-- so here we have LocalEnv free vars in Yaffle

eval locs env (Ref x) = VRef x
eval locs env (App t u) = vapp (eval locs env t) (eval locs env u)
eval locs env U = VU
-- yaffle breaks out binder
eval locs env (Lam x icit t) = VLam x icit (\u => eval (u :: locs) env t)
eval locs env (Pi x icit a b) = VPi x icit (eval locs env a) (\u => eval (u :: locs) env b)
-- This one we need to make 
eval locs env (Let x icit ty t u) = eval (eval locs env t :: locs) env u
eval locs env (Bnd i) = let Just rval = getAt i env | _ => ?out_of_index in rval

vfresh : Nat -> Val
vfresh l = VVar l

export
quote : (k : Nat) -> Val -> Tm
quote l (VVar k) = Bnd (S l `minus` k) -- level to index
quote l (VApp t u) = App (quote l t) (quote l u)
-- so this one is calling the kripke on [x] and a fresh var
quote l (VLam x icit t) = Lam x icit (quote (S l) (t (vfresh l))) -- that one is too big
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (b $ vfresh l))
quote l VU = U
quote _ (VRef n) = Ref n

-- vars -> vars -> vars in yaffle
export
nf : {n : Nat} -> Env -> Tm -> Tm
nf env t = quote n (eval [] env t)

public export
conv : (lvl : Nat) -> Val -> Val -> Bool

data BD = Bound | Defined

public export
Types : Type
Types = List (Name, Lazy Val)

-- REVIEW indices
public export
record Context where
  constructor MkCtx
  env : Env
  types : List (String, Val)
  pos : SourcePos

-- data Env : (tm : SnocList Name -> Type) -> SnocList Name -> Type where

-- Kovacs Small-TT has locals and globals, lets do that.  
-- Still need to sort out the indices - one or two on env?

||| add a binding to environment
extend : { n : Nat} -> Context -> String -> Val -> Context
extend (MkCtx env types pos) name ty =
    MkCtx (VVar (length env) :: env) ((name, ty) :: types) pos


-- weirich has 'hints' to store the claims before the def is seen/checked
-- saying it is unsafe. afterwards they are mixed into the context.
-- idris essentially leaves holes, filled in later, for undefined claims
-- Is it ok to leaving them in there (if they pass checkType) as long as
-- we don't register the def if it fails checking?

-- shoot, I have another of these in Check.idr


-- -- public export
-- record Ctx (n : Nat) where
--   constructor MkCtx
--   env : Env k n     -- for eval
--   types : Types n   -- name lookup, prettyprint
--   bds : Vect n BD  -- meta creation
--   lvl : Nat -- This is n, do we need it?
--   -- Kovacs and Weirich use a position node, Idris has FC
--   pos : SourcePos

-- %name Ctx ctx

-- public export
-- emptyCtx : Ctx Z
-- emptyCtx = MkCtx {k=0} [] [] [] 0 (0,0)

-- find out how pi-forall treats binders
-- Vars are unbound TName 

-- ezoo
-- Tm has Ix
-- Val has Lvl

-- by the time we hit ezoo 5/6, there is a Map string -> (Lvl, Type) for name lookup.

-- smalltt


-- idris



-- public export
-- bindCtx : Name -> Lazy (Val (zz + n))  -> Ctx n -> Ctx (S n)
-- bindCtx x a (MkCtx env types bds l pos) =
--   MkCtx (VVar l :: env) ((x,a) :: map (map thinVal) types) (Bound :: bds) (l+1) pos

-- public export
-- define : Name -> Val -> Lazy (Val)  -> Ctx n -> Ctx (S n)
-- define x v ty (MkCtx env types bds l pos) =
--   MkCtx (v :: env) ((x,ty) :: map (map thinVal) types) (Defined :: bds) (l + 1) pos


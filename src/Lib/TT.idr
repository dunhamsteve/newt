-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

-- The Control.App requires a patched idris. :(

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Data.Fin
import Data.Vect

public export
Name : Type
Name = String

-- Trying to do well-scoped here, so the indices are proven.
-- RIP out the indices

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
Eq Icit where
  Implicit == Implicit = True
  Explicit == Explicit = True
  _ == _ = False

||| Eq on Tm. We've got deBruijn indices, so I'm not comparing names
export
Eq (Tm n) where
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
data Val : Nat -> Type

public export
0 Closure : Nat -> Type

-- IS/TypeTheory.idr is calling this a Kripke function space
-- Yaffle, IS/TypeTheory use a function here.
-- Kovacs, Idris use Env and Tm

-- in cctt kovacs refers to this as defunctionalization vs HOAS
-- https://github.com/AndrasKovacs/cctt/blob/main/README.md#defunctionalization


-- Yaffle is vars -> vars here


Closure n = Val (S n) -> Val n

public export
data Val : Nat -> Type where
  -- This will be local / flex with spine.
  VVar : Fin n -> Val n
  VRef : String -> Val n
  VApp : Val n ->  Lazy (Val n) -> Val n
  VLam : Name -> Icit -> Closure n -> Val n
  VPi : Name -> Icit -> Lazy (Val n) -> Closure n -> Val n
  VU : Val n

||| LocalEnv free vars
public export
LocalEnv : Nat -> Nat -> Type 
LocalEnv k n = Vect k (Val n)

public export
Env : Nat -> Type
Env n = Vect n (Val n)

export
eval : LocalEnv k n -> Env n -> Tm (n + k) -> Val n

thinVal : Val k -> Val (S k)
thinVal (VVar x) = VVar (shift 1 x)
thinVal (VRef str) = VRef str
thinVal (VApp x y) = VApp (thinVal x) (thinVal y)
thinVal (VLam str icit f) = VLam str icit (believe_me f) -- FIXME
thinVal (VPi str icit x f) = VPi str icit (thinVal x) (believe_me f)
thinVal VU = VU


export
vapp : Val n -> Val n -> Val n
vapp (VLam _ icit t) u = t (thinVal u)
vapp t u = VApp t u

-- thinVal : {e : Nat} -> Val k -> Val (e + k)
-- thinVal (VVar x) = VVar (shift _ x)
-- thinVal (VRef str) = VRef str
-- thinVal (VApp x y) = VApp (thinVal x) (thinVal y)
-- thinVal (VLam str icit f) = VLam str icit 
--       (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
-- thinVal (VPi str icit x f) = VPi str icit (thinVal {e} x) 
--       (\g, v => rewrite plusAssociative g e k in f (g + e) (rewrite sym $ plusAssociative g e k in v))
-- thinVal VU = VU



bind :  Val n -> Env n -> Env (S n)
bind v env = thinVal v :: map thinVal env

-- so here we have LocalEnv free vars in Yaffle

eval locs env (Ref x) = VRef x
eval locs env (App t u) = vapp (eval locs env t) (eval locs env u)
eval locs env U = VU
-- yaffle breaks out binder
eval locs env (Lam x icit t) = VLam x icit (\u => (u :: locs) env (rewrite sym $ plusSuccRightSucc n k in t))
eval locs env (Pi x icit a b) = VPi x icit (eval locs env a) (\u => eval (u :: locs) env (rewrite sym $ plusSuccRightSucc n k in b))
-- This one we need to make 
eval locs env (Let x icit ty t u) = eval (eval locs env t :: locs) env (rewrite sym $ plusSuccRightSucc n k in u)
eval locs env (Bnd i) = index i ?hole -- env

vfresh : (l : Nat) -> Val (S l)
vfresh l = VVar last

export
quote : (k : Nat) -> Val k -> Tm k
quote l (VVar k) = Bnd (complement k) -- level to index
quote l (VApp t u) = App (quote l t) (quote l u)
-- so this one is calling the kripke on [x] and a fresh var
quote l (VLam x icit t) = Lam x icit (quote (S l) (believe_me $ t (vfresh l))) -- that one is too big
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (believe_me $ b $ vfresh l))
quote l VU = U
quote _ (VRef n) = Ref n

-- vars -> vars -> vars in yaffle
export
nf : {n : Nat} -> Env n -> Tm n -> Tm n
nf env t = quote n (eval [] env (rewrite plusZeroRightNeutral n in t))

public export
conv : (lvl : Nat) -> Val n -> Val n -> Bool

data BD = Bound | Defined

public export
Types : Nat -> Type
Types n = Vect n (Name, Lazy (Val n))



-- REVIEW indices
public export
record Context (n : Nat)  where
  constructor MkCtx
  
  -- These are values, they'll be the length of the environment
  env : Env n -- Vect n (Val f)

  -- fine for now, consider a map later
  types : Vect n (String, Val n)
  pos : SourcePos

-- data Env : (tm : SnocList Name -> Type) -> SnocList Name -> Type where

-- Kovacs Small-TT has locals and globals, lets do that.  
-- Still need to sort out the indices - one or two on env?

||| add a binding to environment
extend : { n : Nat} -> Context n -> String -> Val n -> Context (S n)
extend (MkCtx env types pos) name ty with (length env)
  _ | l = 
    
    let types' = Data.Vect.(::) (name, thinVal ty)   (map (map thinVal) types) in
    let l' : Fin (S n) := last in
    MkCtx {n=S n} (VVar l' :: map thinVal env) types' pos
    -- ?hole_0 --  { env  := (Val (length env.(Context env types pos)) :: (Context env types pos).env), types := (n, ty) :: (Context env types pos).types  } (Context env types pos)


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
-- define : Name -> Val n -> Lazy (Val n)  -> Ctx n -> Ctx (S n)
-- define x v ty (MkCtx env types bds l pos) =
--   MkCtx (v :: env) ((x,ty) :: map (map thinVal) types) (Defined :: bds) (l + 1) pos


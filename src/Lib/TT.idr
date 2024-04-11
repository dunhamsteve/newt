-- I'm not sure this is related, or just a note to self (Presheaves on Porpoise)
-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

-- The Control.App requires a patched idris. :(

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Control.Monad.Error.Interface
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

public export
Show Tm where
  show (Bnd k) = "Bnd \{show k}"
  show (Ref str) = "Ref \{show str}"
  show (Lam nm Implicit t) = "(λ {\{nm}} => \{show  t})"
  show (Lam nm Explicit t) = "(λ \{nm}  => \{show  t})"
  show (App t u) = "(\{show t} \{show u})"
  show U = "U"
  show (Pi str icit t u) = "(∏ \{str} : \{show t} => \{show u})"
  show (Let str icit t u v) = "let \{str} : \{show t} = \{show u} in \{show v}"

-- I can't really show val because it's HOAS...

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

public export
Env : Type
Env = List Val

export
eval : Env -> Tm -> Val

export
vapp : Val -> Val -> Val
vapp (VLam _ icit t) u = t u
vapp t u = VApp t u

bind : Val -> Env -> Env
bind v env = v :: env

-- so here we have LocalEnv free vars in Yaffle

eval env (Ref x) = VRef x
eval env (App t u) = vapp (eval env t) (eval env u)
eval env U = VU
-- yaffle breaks out binder
eval env (Lam x icit t) = VLam x icit (\u => eval (u :: env) t)
eval env (Pi x icit a b) = VPi x icit (eval env a) (\u => eval (u :: env) b)
-- This one we need to make 
eval env (Let x icit ty t u) = eval (eval env t :: env) u
eval env (Bnd i) = let Just rval = getAt i env | _ => ?out_of_index
                   in rval

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
nf env t = quote n (eval env t)

public export
conv : (lvl : Nat) -> Val -> Val -> Bool

-- data BD = Bound | Defined

-- public export
-- Types : Type
-- Types = List (Name, Lazy Val)


public export
record Context where
  constructor MkCtx
  env : Env                  -- Values in scope
  types : List (String, Val) -- types and names in scope
  -- bds  : List BD          -- bind or define
  -- lvl = length types
  pos : SourcePos            -- the last SourcePos that we saw



export
empty : Context
empty = MkCtx [] [] (0,0)

export partial
Show Context where
  show ctx = "Context \{show $ map fst $ ctx.types}"

-- Kovacs Small-TT has locals and globals, lets do that.  

||| add a binding to environment
export
extend : Context -> String -> Val -> Context
extend (MkCtx env types pos) name ty =
    MkCtx (VVar (length env) :: env) ((name, ty) :: types) pos

lookup : {0 m : Type -> Type} -> {auto _ : MonadError String m} ->
      Context -> String -> m Val
lookup ctx nm = go ctx.types
  where
    go : List (String,Val) -> m Val
    go [] = throwError "Name \{nm} not in scope"
    go ((n, ty) :: xs) = if n == nm then pure ty else go xs


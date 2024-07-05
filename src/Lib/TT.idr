-- I'm not sure this is related, or just a note to self (Presheaves on Porpoise)

-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Lib.Prettier

import Control.Monad.Error.Interface
import Data.Fin
import Data.List
import Data.Vect
import Data.SortedMap

public export
Name : Type
Name = String

public export
data Icit = Implicit | Explicit

%name Icit icit

public export
data Tm : Type where
  Bnd : Nat -> Tm
  -- Maybe Def here instead of Maybe Tm, we'll have DCon, TCon, etc.
  Ref : String -> Maybe Tm -> Tm
  Lam : Name -> Icit -> Tm -> Tm
  App : Tm -> Tm -> Tm
  U   : Tm
  Pi  : Name -> Icit -> Tm -> Tm -> Tm
  Let : Name -> Icit -> Tm -> Tm -> Tm -> Tm

%name Tm t, u, v

public export
Show Tm where
  show (Bnd k) = "(Bnd \{show k})"
  show (Ref str _) = "(Ref \{show str})"
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
  (Ref x _) == (Ref y _) = x == y
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
data Closure : Type

public export
data Val : Type where
  -- This will be local / flex with spine.
  VVar : Nat -> Val
  VRef : String -> Maybe Tm -> Val
  VApp : Val ->  Lazy (Val) -> Val
  VLam : Name -> Icit -> Closure -> Val
  VPi : Name -> Icit -> Lazy Val -> Closure -> Val
  VU : Val

public export
Env : Type
Env = List Val

public export
data Mode = CBN | CBV

export
eval : Env -> Mode -> Tm -> Val

data Closure = MkClosure Env Tm

public export
($$) : {auto mode : Mode} -> Closure -> Val -> Val
($$) (MkClosure env tm) u = eval (u :: env) mode tm

public export
infixl 8 $$

export
vapp : Val -> Val -> Val
vapp (VLam _ icit t) u = t $$ u
vapp t u = VApp t u

bind : Val -> Env -> Env
bind v env = v :: env

-- Do we want a def in here instead?  We'll need DCon/TCon eventually
-- I need to be aggressive about reduction, I guess. I'll figure it out
-- later, maybe need lazy glued values.
eval env mode (Ref x (Just tm)) = eval env mode tm
eval env mode (Ref x Nothing) = VRef x Nothing
eval env mode (App (Ref x (Just tm)) u) = vapp (eval env mode tm) (eval env mode u)
eval env mode (App t u) = vapp (eval env mode t) (eval env mode u)
eval env mode U = VU
eval env mode (Lam x icit t) = VLam x icit (MkClosure env t)
eval env mode (Pi x icit a b) = VPi x icit (eval env mode a) (MkClosure env b)
eval env mode (Let x icit ty t u) = eval (eval env mode t :: env) mode u
eval env mode (Bnd i) = let Just rval = getAt i env | _ => ?out_of_index
                   in rval

export
quote : (lvl : Nat) -> Val -> Tm
quote l (VVar k) = Bnd ((l `minus` k) `minus` 1) -- level to index
quote l (VApp t u) = App (quote l t) (quote l u)
quote l (VLam x icit t) = Lam x icit (quote (S l) (t $$ VVar l))
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (b $$ VVar l))
quote l VU = U
quote l (VRef n tm) = Ref n tm

-- how are we using this?  Can we assume completely closed?
-- ezoo only seems to use it at [], but essentially does this:
export
nf : Env -> Tm -> Tm
nf env t = quote (length env) (eval env CBN t)

public export
conv : (lvl : Nat) -> Val -> Val -> Bool


{-
smalltt

smalltt gets into weird haskell weeds in eval - shifting top level to the left
and tagging meta vs top with a bit.

I think something subtle is going on with laziness on Elaboration.hs:300
yeah, and define is even inlined.

So it has a top context, and clears out almost everything for processing a def in
a different kind of context.

we very much need an idea of local context for metas. I don't want to abstract over
the entire program.

So I guess we have top and local then?

With haskell syntax. I think we can have Axiom for claims and rewrite to def later.

Hmm, so given ezoo, if I'm going simple, I could keep BDs short, and use the normal
context. (Zoo4.lean:222) I'd probably still need an undefined/axiom marker as a value? 

ok, so with just one context, Env is List Val and we're getting Tm back from type checking.

Can I get val back? Do we need to quote? What happens if we don't?

-}

data BD = Bound | Defined

-- we'll use this for typechecking, but need to keep a TopContext around too.
public export
record Context where
  constructor MkCtx
  lvl : Nat
  -- shall we use lvl as an index?
  env : Env                  -- Values in scope
  types : Vect lvl (String, Val) -- types and names in scope
  -- so we'll try "bds" determines length of local context
  bds  : List BD          -- bound or defined
  
  pos : SourcePos            -- the last SourcePos that we saw

export
empty : Context
empty = MkCtx 0 [] [] [] (0,0)

export partial
Show Context where
  show ctx = "Context \{show $ map fst $ ctx.types}"

-- TODO Pretty Context



-- idea cribbed from pi-forall
public export
data ErrorSeg : Type where
  DD : Pretty a => a -> ErrorSeg
  DS : String -> ErrorSeg

toDoc : ErrorSeg -> Doc
toDoc (DD x) = pretty x
toDoc (DS str) = text str

export
error : {0 m : Type -> Type} -> {auto _ : MonadError Error m} ->
    {auto ctx : Context} -> List ErrorSeg -> m a
error xs = throwError $ E ctx.pos (render 80 $ spread $ map toDoc xs)

||| add a binding to environment
export
extend : Context -> String -> Val -> Context
extend (MkCtx lvl env types bds pos) name ty =
    MkCtx (S lvl) (VVar lvl :: env) ((name, ty) :: types) (Bound :: bds) pos

-- I guess we define things as values?
export
define : Context -> String -> Val -> Val -> Context
define (MkCtx lvl env types bds pos) name val ty =
  MkCtx (S lvl) (val :: env) ((name, ty) :: types) (Defined :: bds) pos

-- not used
lookup : {0 m : Type -> Type} -> {auto _ : MonadError String m} ->
      Context -> String -> m Val
lookup ctx nm = go ctx.types
  where
    go : Vect n (String,Val) -> m Val
    go [] = throwError "Name \{nm} not in scope"
    go ((n, ty) :: xs) = if n == nm then pure ty else go xs



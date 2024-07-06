-- I'm not sure this is related, or just a note to self (Presheaves on Porpoise)

-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Metas

import Control.Monad.Error.Interface

import Data.IORef
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
data BD = Bound | Defined


public export
data Tm : Type where
  Bnd : Nat -> Tm
  -- Maybe Def here instead of Maybe Tm, we'll have DCon, TCon, etc.
  Ref : String -> Maybe Tm -> Tm
  Meta : Nat -> Tm
  -- kovacs optimization, I think we can App out meta instead
  -- InsMeta : Nat -> List BD -> Tm
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
  show (Meta i) = "(Meta \{show i})"
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

public export
Pretty Tm where
  pretty (Bnd k) = ?rhs_0
  pretty (Ref str mt) = text str
  pretty (Meta k) = text "?m\{show k}"
  pretty (Lam str Implicit t) = text "(\\ {\{str}} => " <+> pretty t <+> ")"
  pretty (Lam str Explicit t) = text "(\\ \{str} => " <+> pretty t <+> ")"
  pretty (App t u) = text "(" <+> pretty t <+> pretty u <+> ")"
  pretty U = "U"
  pretty (Pi str icit t u) = text "(" <+> text str <+> ":" <+> pretty t <+> "=>" <+> pretty u <+> ")"
  pretty (Let str icit t u v) = text "let" <+> text str <+> ":" <+> pretty t <+> "=" <+> pretty u

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
  VVar : (k : Nat) -> (sp : List Val) -> Val
  -- I wanted the Maybe Tm in here, but for now we're always expanding.
  -- Maybe this is where I glue
  VRef : (nm : String) -> (sp : List Val) -> Val
  -- we'll need to look this up in ctx with IO
  VMeta : (ix : Nat) -> (sp : List Val) -> Val
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
vapp (VVar k sp) u = VVar k (u :: sp)
vapp (VRef nm sp) u = VRef nm (u :: sp)
vapp (VMeta k sp) u = VMeta k (u :: sp)
vapp _ _ = ?throw_impossible

bind : Val -> Env -> Env
bind v env = v :: env

-- Do we want a def in here instead?  We'll need DCon/TCon eventually
-- I need to be aggressive about reduction, I guess. I'll figure it out
-- later, maybe need lazy glued values.
eval env mode (Ref x (Just tm)) = eval env mode tm
eval env mode (Ref x Nothing) = VRef x []
eval env mode (App (Ref x (Just tm)) u) = vapp (eval env mode tm) (eval env mode u)
eval env mode (App t u) = vapp (eval env mode t) (eval env mode u)
eval env mode U = VU
eval env mode (Meta i) = VMeta i []
eval env mode (Lam x icit t) = VLam x icit (MkClosure env t)
eval env mode (Pi x icit a b) = VPi x icit (eval env mode a) (MkClosure env b)
eval env mode (Let x icit ty t u) = eval (eval env mode t :: env) mode u
eval env mode (Bnd i) = let Just rval = getAt i env | _ => ?out_of_index
                   in rval

export
quote : (lvl : Nat) -> Val -> Tm

quoteSp : (lvl : Nat) -> Tm -> List Val -> Tm
quoteSp lvl t [] = t
quoteSp lvl t (x :: xs) = quoteSp lvl (App t (quote lvl x)) xs

quote l (VVar k sp) = quoteSp l (Bnd ((l `minus` k) `minus` 1)) sp -- level to index
quote l (VMeta i sp) = quoteSp l (Meta i) sp
quote l (VLam x icit t) = Lam x icit (quote (S l) (t $$ VVar l []))
quote l (VPi x icit a b) = Pi x icit (quote l a) (quote (S l) (b $$ VVar l []))
quote l VU = U
quote l (VRef n sp) = quoteSp l (Ref n Nothing) sp

-- Can we assume closed terms?
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


public export
data MetaEntry = Unsolved Nat (List BD) | Solved Nat Tm (List BD)

public export
record MetaContext where
  constructor MC
  metas : List MetaEntry
  next : Nat


public export
data Def = Axiom | TCon (List String) | DCon Nat | Fn Tm

Show Def where
  show Axiom = "axiom"
  show (TCon strs) = "TCon \{show strs}"
  show (DCon k) = "DCon \{show k}"
  show (Fn t) = "Fn \{show t}"

||| entry in the top level context
public export
record TopEntry where
  constructor MkEntry
  name : String
  type : Tm
  def : Def

-- FIXME snoc

export
Show TopEntry where
  show (MkEntry name type def) = "\{name} : \{show type} := \{show def}"

||| Top level context.
||| Most of the reason this is separate is to have a different type
||| `Def` for the entries.
|||
||| The price is that we have names in addition to levels. Do we want to
||| expand these during conversion?
public export
record TopContext where
  constructor MkTop
  -- We'll add a map later?
  defs : List TopEntry
  metas : IORef MetaContext
  -- metas : TODO

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
  
  -- We only need this here if we don't pass TopContext
  -- top : TopContext
  metas : IORef MetaContext

export
freshMeta : HasIO m => Context -> m Tm
freshMeta ctx = do
  mc <- readIORef ctx.metas
  writeIORef ctx.metas $ { next $= S, metas $= (Unsolved mc.next ctx.bds ::) } mc
  pure $ applyBDs 0 (Meta mc.next) ctx.bds 
  where
  -- hope I got the right order here :)
  applyBDs : Nat -> Tm -> List BD -> Tm
  applyBDs k t [] = t
  applyBDs k t (Bound :: xs) = applyBDs (S k) (App t (Bnd k)) xs
  applyBDs k t (Defined :: xs) = applyBDs (S k) t xs

-- we need more of topcontext later - Maybe switch it up so we're not passing
-- around top
export
mkCtx : IORef MetaContext -> Context
mkCtx metas = MkCtx 0 [] [] [] (0,0) metas

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
extend ctx name ty =
    { lvl $= S, env $= (VVar ctx.lvl [] ::), types $= ((name, ty) ::), bds $= (Bound ::) } ctx
    
-- I guess we define things as values?
export
define : Context -> String -> Val -> Val -> Context
define ctx name val ty =
  { lvl $= S, env $= (val ::), types $= ((name,ty) ::), bds $= (Defined ::) } ctx


-- not used
lookup : {0 m : Type -> Type} -> {auto _ : MonadError String m} ->
      Context -> String -> m Val
lookup ctx nm = go ctx.types
  where
    go : Vect n (String,Val) -> m Val
    go [] = throwError "Name \{nm} not in scope"
    go ((n, ty) :: xs) = if n == nm then pure ty else go xs



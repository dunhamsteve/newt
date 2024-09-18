module Lib.Types

-- For FC, Error
import public Lib.Parser.Impl
import Lib.Prettier

import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.State

import Data.Fin
import Data.IORef
import Data.List
import Data.SnocList
import Data.SortedMap
import Data.String
import Data.Vect

public export
Name : Type
Name = String

public export
data Icit = Implicit | Explicit

%name Icit icit

export
Show Icit where
  show Implicit = "Implicit"
  show Explicit = "Explicit"

public export
data BD = Bound | Defined

Show BD where
  show Bound = "bnd"
  show Defined = "def"


-- do we just admit string names for these and let the prim functions
-- sort it out?
-- I'd like Int / String to have syntax

data PrimType = StringType | IntType

data PrimVal : Type where
  PrimString : String -> PrimVal
  PrimInt : Int -> PrimVal

public export
data Tm : Type

public export
data CaseAlt : Type where
  CaseDefault : Tm -> CaseAlt
  -- I've also seen a list of stuff that gets replaced
  CaseCons : (name : String) -> (args : List String) -> Tm ->  CaseAlt
  -- CaseLit : Literal -> Tm ->  CaseAlt

data Def : Type

public export
data Literal = LString String | LInt Int

Show Literal where
  show (LString str) = show str
  show (LInt i) = show i

data Tm : Type where
  Bnd : FC -> Nat -> Tm
  -- Maybe Def here instead of Maybe Tm, we'll have DCon, TCon, etc.
  Ref : FC -> String -> Def -> Tm
  Meta : FC -> Nat -> Tm
  -- kovacs optimization, I think we can App out meta instead
  -- InsMeta : Nat -> List BD -> Tm
  Lam : FC -> Name -> Tm -> Tm
  App : FC -> Tm -> Tm -> Tm
  U   : FC -> Tm
  Pi  : FC -> Name -> Icit -> Tm -> Tm -> Tm
  -- REVIEW - do we want to just push it up like idris?
  Case : FC -> Tm -> List CaseAlt -> Tm
  -- need type?
  Let : FC -> Name -> Tm -> Tm -> Tm
  Lit : FC -> Literal -> Tm

%name Tm t, u, v

export
HasFC Tm where
  getFC (Bnd fc k) = fc
  getFC (Ref fc str x) = fc
  getFC (Meta fc k) = fc
  getFC (Lam fc str t) = fc
  getFC (App fc t u) = fc
  getFC (U fc) = fc
  getFC (Pi fc str icit t u) = fc
  getFC (Case fc t xs) = fc
  getFC (Lit fc _) = fc
  getFC (Let fc _ _ _) = fc

covering
Show Tm

covering
Show CaseAlt where
  show (CaseDefault tm) = "_ => \{show tm}"
  show (CaseCons nm args tm) = "\{nm} \{unwords args} => \{show tm}"

-- public export
covering
Show Tm where
  show (Bnd _ k) = "(Bnd \{show k})"
  show (Ref _ str _) = "(Ref \{show str})"
  show (Lam _ nm t) = "(\\ \{nm}  => \{show  t})"
  show (App _ t u) = "(\{show t} \{show u})"
  show (Meta _ i) = "(Meta \{show i})"
  show (Lit _ l) = "(Lit \{show l})"
  show (U _) = "U"
  show (Pi _ str Explicit t u) = "(Pi (\{str} : \{show t}) => \{show u})"
  show (Pi _ str Implicit t u) = "(Pi {\{str} : \{show t}} => \{show u})"
  show (Case _ sc alts) = "(Case \{show sc} \{show alts})"
  show (Let _ nm t u) = "(Let \{nm} \{show t} \{show u})"

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
  (Bnd _ x) == (Bnd _ y) = x == y
  (Ref _ x _) == Ref _ y _ = x == y
  (Lam _ n t) == Lam _ n' t' = t == t'
  (App _ t u) == App _ t' u' = t == t' && u == u'
  (U _) == (U _) = True
  (Pi _ n icit t u) == (Pi _ n' icit' t' u') = icit == icit' && t == t' && u == u'
  _ == _ = False


||| Pretty printer for Tm.
export
pprint : List String -> Tm -> String
pprint names tm = render 80 $ go names tm
  where
    go : List String -> Tm -> Doc
    goAlt : List String -> CaseAlt -> Doc

    goAlt names (CaseDefault t) = "_" <+> "=>" <+> go ("_" :: names) t
    goAlt names (CaseCons name args t) = text name <+> spread (map text args) <+> "=>" <+> go (args ++ names) t

    go names (Bnd _ k) = case getAt k names of
      Nothing => text "BND:\{show k}"
      Just nm => text "\{nm}:\{show k}"
    go names (Ref _ str mt) = text str
    go names (Meta _ k) = text "?m:\{show k}"
    go names (Lam _ nm t) = text "(\\ \{nm} =>" <+> go (nm :: names) t <+> ")"
    go names (App _ t u) = text "(" <+> go names t <+> go names u <+> ")"
    go names (U _) = "U"
    go names (Pi _ nm Implicit t u) =
      text "({" <+> text nm <+> ":" <+> go names t <+> "}" <+> "->" <+> go (nm :: names) u <+> ")"
    go names (Pi _ nm Explicit t u) =
      text "((" <+> text nm <+> ":" <+> go names t <+> ")" <+> "->" <+> go (nm :: names) u <+> ")"
    -- FIXME - probably way wrong on the names here.  There is implicit binding going on
    go names (Case _ sc alts) = text "case" <+> go names sc <+> text "of" </> (nest 2 (line ++ stack (map (goAlt names) alts)))
    go names (Lit _ lit) = text "\{show lit}"
    go names (Let _ nm t u) = text "let" <+> text nm <+> ":=" <+> go names t </> (nest 2 $ go names u)

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
  VVar : FC -> (k : Nat) -> (sp : SnocList Val) -> Val
  -- I wanted the Maybe Tm in here, but for now we're always expanding.
  -- Maybe this is where I glue
  VRef : FC -> (nm : String) -> Def -> (sp : SnocList Val) -> Val
  -- neutral case
  VCase : FC -> (sc : Val) -> List CaseAlt -> Val
  -- we'll need to look this up in ctx with IO
  VMeta : FC -> (ix : Nat) -> (sp : SnocList Val) -> Val
  VLam : FC -> Name -> Closure -> Val
  VPi : FC -> Name -> Icit -> (a : Lazy Val) -> (b : Closure) -> Val
  VLet : FC -> Name -> Val -> (b : Closure) -> Val
  VU : FC -> Val
  VLit : FC -> Literal -> Val

public export
getValFC : Val -> FC
getValFC (VVar fc _ _) = fc
getValFC (VRef fc _ _ _) = fc
getValFC (VCase fc _ _) = fc
getValFC (VMeta fc _ _) = fc
getValFC (VLam fc _ _) = fc
getValFC (VPi fc _ _ a b) = fc
getValFC (VU fc) = fc
getValFC (VLit fc _) = fc


Show Closure

covering export
Show Val where
  show (VVar _ k sp) = "(%var \{show k} \{show sp})"
  show (VRef _ nm _ sp) = "(%ref \{nm} \{show sp})"
  show (VMeta _ ix sp) = "(%meta \{show ix} \{show sp})"
  show (VLam _ str x) = "(%lam \{str} \{show x})"
  show (VPi fc str Implicit x y) = "(%pi {\{str} : \{show  x}}. \{show  y})"
  show (VPi fc str Explicit x y) = "(%pi (\{str} : \{show  x}). \{show  y})"
  show (VCase fc sc alts) = "(%case \{show sc} ...)"
  show (VU _) = "U"
  show (VLit _ lit) = show lit

-- Not used - I was going to change context to have a List Binder
-- instead of env, types, bds
-- But when we get down into eval, we don't have types to put into the env
-- It looks like Idris has a separate LocalEnv in eval, Kovacs peels off
-- env from context and extends it.
data Binder : Type where
  Bind : (nm : String) -> (bd : BD) -> (val : Val) -> (ty : Val) -> Binder

covering
Show Binder where
  show (Bind nm bd val ty) = "(\{show bd} \{show nm} \{show val} : \{show ty})"

public export
Env : Type
Env = List Val

public export
data Mode = CBN | CBV

public export
data Closure = MkClosure Env Tm

covering
Show Closure where
  show (MkClosure xs t) = "(%cl \{show xs} \{show t})"
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

record Context

public export
data MetaEntry = Unsolved FC Nat Context Val | Solved Nat Val

export
covering
Show MetaEntry where
  show (Unsolved pos k xs ty) = "Unsolved \{show pos} \{show k} : \{show ty}"
  show (Solved k x) = "Solved \{show k} \{show x}"

public export
record MetaContext where
  constructor MC
  metas : List MetaEntry
  next : Nat


public export
data Def = Axiom | TCon (List String) | DCon Nat String | Fn Tm | PrimTCon | PrimFn String

public export
covering
Show Def where
  show Axiom = "axiom"
  show (TCon strs) = "TCon \{show strs}"
  show (DCon k tyname) = "DCon \{show k} \{show tyname}"
  show (Fn t) = "Fn \{show t}"
  show (PrimTCon) = "PrimTCon"
  show (PrimFn src) = "PrimFn \{show src}"

||| entry in the top level context
public export
record TopEntry where
  constructor MkEntry
  name : String
  type : Tm
  def : Def

-- FIXME snoc

export
covering
Show TopEntry where
  show (MkEntry name type def) = "\{name} : \{show type} := \{show def}"

||| Top level context.
||| Most of the reason this is separate is to have a different type
||| `Def` for the entries.
|||
||| The price is that we have names in addition to levels. Do we want to
||| expand these during normalization?
public export
record TopContext where
  constructor MkTop
  -- We'll add a map later?
  defs : List TopEntry
  metas : IORef MetaContext
  verbose : Bool
  -- metas : TODO



-- we'll use this for typechecking, but need to keep a TopContext around too.
public export
record Context where
  [noHints]
  constructor MkCtx
  lvl : Nat
  -- shall we use lvl as an index?
  env : Env                  -- Values in scope
  types : Vect lvl (String, Val) -- types and names in scope
  -- so we'll try "bds" determines length of local context
  bds : Vect lvl BD          -- bound or defined

  -- We only need this here if we don't pass TopContext
  -- top : TopContext
  metas : IORef MetaContext
  fc : FC

export withPos : Context -> FC -> Context
withPos ctx fc = { fc := fc } ctx

export
names : Context -> List String
names ctx = toList $ map fst ctx.types

public export
M : Type -> Type
M = (StateT TopContext (EitherT Impl.Error IO))

-- we need more of topcontext later - Maybe switch it up so we're not passing
-- around top
export
mkCtx : IORef MetaContext -> FC -> Context
mkCtx metas fc = MkCtx 0 [] [] [] metas fc

||| Force argument and print if verbose is true
export
debug : Lazy String -> M ()
debug x = do
  top <- get
  when top.verbose $ putStrLn x

||| Version of debug that makes monadic computation lazy
export
debugM : M String -> M ()
debugM x = do
  top <- get
  when top.verbose $ do putStrLn !(x)

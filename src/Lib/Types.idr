module Lib.Types

-- For FC, Error
import public Lib.Common
import public Lib.Prettier

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
data Icit = Implicit | Explicit | Auto

%name Icit icit

export
Show Icit where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show Auto = "Auto"

public export
data BD = Bound | Defined

public export
Eq BD where
  Bound == Bound = True
  Defined == Defined = True
  _ == _ = False

public export
Show BD where
  show Bound = "bnd"
  show Defined = "def"

public export
data Quant = Zero | Many

public export
Show Quant where
  show Zero = "0 "
  show Many = ""

Eq Quant where
  Zero == Zero = True
  Many == Many = True
  _ == _ = False

-- We could make this polymorphic and use for environment...
public export
data BindInfo : Type where
  BI : (fc : FC) -> (name : Name) -> (icit : Icit) -> (quant : Quant) -> BindInfo

%name BindInfo bi

public export
HasFC BindInfo where
  getFC (BI fc _ _ _) = fc

-- do we just admit string names for these and let the prim functions
-- sort it out?
-- I'd like Int / String to have syntax

data PrimType = StringType | IntType

data PrimVal : Type where
  PrimString : String -> PrimVal
  PrimInt : Int -> PrimVal
  PrimChar : Char -> PrimVal

public export
data Tm : Type

public export
data Literal = LString String | LInt Int | LChar Char

%name Literal lit

public export
Show Literal where
  show (LString str) = show str
  show (LInt i) = show i
  show (LChar c) = show c

public export
data CaseAlt : Type where
  CaseDefault : Tm -> CaseAlt
  CaseCons : (name : String) -> (args : List String) -> Tm ->  CaseAlt
  CaseLit : Literal -> Tm ->  CaseAlt

data Def : Type


public export
Eq Literal where
  LString x == LString y = x == y
  LInt x == LInt y = x == y
  LChar x == LChar y = x == y
  _ == _ = False

data Tm : Type where
  Bnd : FC -> Nat -> Tm
  -- Maybe Def here instead of Maybe Tm, we'll have DCon, TCon, etc.
  Ref : FC -> String -> Def -> Tm
  Meta : FC -> Nat -> Tm
  -- kovacs optimization, I think we can App out meta instead
  -- InsMeta : Nat -> List BD -> Tm
  Lam : FC -> Name -> Icit -> Quant -> Tm -> Tm
  App : FC -> Tm -> Tm -> Tm
  U   : FC -> Tm
  Pi  : FC -> Name -> Icit -> Quant -> Tm -> Tm -> Tm
  Case : FC -> Tm -> List CaseAlt -> Tm
  -- need type?
  Let : FC -> Name -> Tm -> Tm -> Tm
  -- for desugaring where
  LetRec : FC -> Name -> Tm -> Tm -> Tm
  Lit : FC -> Literal -> Tm
  Erased : FC -> Tm

%name Tm t, u, v

export
HasFC Tm where
  getFC (Bnd fc k) = fc
  getFC (Ref fc str x) = fc
  getFC (Meta fc k) = fc
  getFC (Lam fc str _ _ t) = fc
  getFC (App fc t u) = fc
  getFC (U fc) = fc
  getFC (Pi fc str icit quant t u) = fc
  getFC (Case fc t xs) = fc
  getFC (Lit fc _) = fc
  getFC (Let fc _ _ _) = fc
  getFC (LetRec fc _ _ _) = fc
  getFC (Erased fc) = fc

covering
Show Tm

public export covering
Show CaseAlt where
  show (CaseDefault tm) = "_ => \{show tm}"
  show (CaseCons nm args tm) = "\{nm} \{unwords args} => \{show tm}"
  show (CaseLit lit tm) = "\{show lit} => \{show tm}"

public export covering
Show Tm where
  show (Bnd _ k) = "(Bnd \{show k})"
  show (Ref _ str _) = "(Ref \{show str})"
  show (Lam _ nm icit rig t) = "(\\ \{show rig}\{nm}  => \{show  t})"
  show (App _ t u) = "(\{show t} \{show u})"
  show (Meta _ i) = "(Meta \{show i})"
  show (Lit _ l) = "(Lit \{show l})"
  show (U _) = "U"
  show (Pi _ str Explicit rig t u) = "(Pi (\{show rig}\{str} : \{show t}) => \{show u})"
  show (Pi _ str Implicit rig t u) = "(Pi {\{show rig}\{str} : \{show t}} => \{show u})"
  show (Pi _ str Auto rig t u) = "(Pi {{\{show rig}\{str} : \{show t}}} => \{show u})"
  show (Case _ sc alts) = "(Case \{show sc} \{show alts})"
  show (Let _ nm t u) = "(Let \{nm} \{show t} \{show u})"
  show (LetRec _ nm t u) = "(LetRec \{nm} \{show t} \{show u})"
  show (Erased _) = "ERASED"

public export
showTm : Tm -> String
showTm = show

-- I can't really show val because it's HOAS...

-- TODO derive
export
Eq Icit where
  Implicit == Implicit = True
  Explicit == Explicit = True
  Auto == Auto = True
  _ == _ = False

||| Eq on Tm. We've got deBruijn indices, so I'm not comparing names
export
Eq (Tm) where
  -- (Local x) == (Local y) = x == y
  (Bnd _ x) == (Bnd _ y) = x == y
  (Ref _ x _) == Ref _ y _ = x == y
  (Lam _ n _ _ t) == Lam _ n' _ _ t' = t == t'
  (App _ t u) == App _ t' u' = t == t' && u == u'
  (U _) == (U _) = True
  (Pi _ n icit rig t u) == (Pi _ n' icit' rig' t' u') = icit == icit' && rig == rig' && t == t' && u == u'
  _ == _ = False



-- TODO App and Lam should have <+/> but we need to fix
-- INFO pprint to `nest 2 ...`
-- maybe return Doc and have an Interpolation..
-- If we need to flatten, case is going to get in the way.

||| Pretty printer for Tm.
export
pprint : List String -> Tm -> Doc
pprint names tm = go 0 names tm
  where
    parens : Nat -> Nat -> Doc -> Doc
    parens a b doc = if a < b
      then text "(" ++ doc ++ text ")"
      else doc

    go : Nat -> List String -> Tm -> Doc
    goAlt : Nat -> List String -> CaseAlt -> Doc

    goAlt p names (CaseDefault t) = "_" <+> "=>" <+> go p ("_" :: names) t
    goAlt p names (CaseCons name args t) = text name <+> spread (map text args) <+> (nest 2 $ "=>" <+/> go p (reverse args ++ names) t)
    -- `;` is not in surface syntax, but sometimes we print on one line
    goAlt p names (CaseLit lit t) = text (show lit) <+> (nest 2 $ "=>" <+/> go p names t ++ ";")

    go p names (Bnd _ k) = case getAt k names of
      -- Either a bug or we're printing without names
      Nothing => text "BND:\{show k}"
      Just nm => text "\{nm}:\{show k}"
    go p names (Ref _ str mt) = text str
    go p names (Meta _ k) = text "?m:\{show k}"
    go p names (Lam _ nm icit quant t) = parens 0 p $ nest 2 $ text "\\ \{show quant}\{nm} =>" <+/> go 0 (nm :: names) t
    go p names (App _ t u) = parens 0 p $ go 0 names t <+> go 1 names u
    go p names (U _) = "U"
    go p names (Pi _ nm Auto rig t u) = parens 0 p $
      text "{{" ++ text (show rig) <+> text nm <+> ":" <+> go 0 names t <+> "}}" <+> "->" <+> go 0 (nm :: names) u
    go p names (Pi _ nm Implicit rig t u) = parens 0 p $
      text "{" ++ text (show rig) <+> text nm <+> ":" <+> go 0 names t <+> "}" <+> "->" <+> go 0 (nm :: names) u
    go p names (Pi _ "_" Explicit Many t u) =
      parens 0 p $ go 1 names t <+> "->" <+> go 0 ("_" :: names) u
    go p names (Pi _ nm Explicit rig t u) = parens 0 p $
      text "(" ++  text (show rig) <+> text nm <+> ":" <+> go 0 names t ++ ")" <+> "->" <+> go 0 (nm :: names) u
    -- FIXME - probably way wrong on the names here.  There is implicit binding going on
    go p names (Case _ sc alts) = parens 0 p $ text "case" <+> go 0 names sc <+> text "of" ++ (nest 2 (line ++ stack (map (goAlt 0 names) alts)))
    go p names (Lit _ lit) = text (show lit)
    go p names (Let _ nm t u) = parens 0 p $ text "let" <+> text nm <+> ":=" <+> go 0 names t <+> "in" </> (nest 2 $ go 0 (nm :: names) u)
    go p names (LetRec _ nm t u) = parens 0 p $ text "letrec" <+> text nm <+> ":=" <+> go 0 names t <+> "in" </> (nest 2 $ go 0 (nm :: names) u)
    go p names (Erased _) = "ERASED"
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
  VLam : FC -> Name -> Icit -> Quant -> Closure -> Val
  VPi : FC -> Name -> Icit -> Quant -> (a : Lazy Val) -> (b : Closure) -> Val
  VLet : FC -> Name -> Val -> Val -> Val
  VLetRec : FC -> Name -> Val -> Val -> Val
  VU : FC -> Val
  VErased : FC -> Val
  VLit : FC -> Literal -> Val

public export
getValFC : Val -> FC
getValFC (VVar fc _ _) = fc
getValFC (VRef fc _ _ _) = fc
getValFC (VCase fc _ _) = fc
getValFC (VMeta fc _ _) = fc
getValFC (VLam fc _ _ _ _) = fc
getValFC (VPi fc _ _ _ a b) = fc
getValFC (VU fc) = fc
getValFC (VErased fc) = fc
getValFC (VLit fc _) = fc
getValFC (VLet fc _ _ _) = fc
getValFC (VLetRec fc _ _ _) = fc


public export
HasFC Val where getFC = getValFC

Show Closure

covering export
Show Val where
  show (VVar _ k [<]) = "%var\{show k}"
  show (VVar _ k sp) = "(%var\{show k} \{unwords $ map show (sp <>> [])})"
  show (VRef _ nm _ [<]) = nm
  show (VRef _ nm _ sp) = "(\{nm} \{unwords $ map show (sp <>> [])})"
  show (VMeta _ ix sp) = "(%meta \{show ix} [\{show $ length sp} sp])"
  show (VLam _ str icit quant x) = "(%lam \{show quant}\{str} \{show x})"
  show (VPi fc str Implicit rig x y) = "(%pi {\{show rig} \{str} : \{show  x}}. \{show  y})"
  show (VPi fc str Explicit rig x y) = "(%pi (\{show rig} \{str} : \{show  x}). \{show  y})"
  show (VCase fc sc alts) = "(%case \{show sc} ...)"
  show (VU _) = "U"
  show (VLit _ lit) = show lit
  show (VLet _ nm a b) = "(%let \{show nm} = \{show a} in \{show b}"
  show (VLetRec _ nm a b) = "(%letrec \{show nm} = \{show a} in \{show b}"
  show (VErased _) = "ERASED"

public export
Env : Type
Env = List Val

public export
data Mode = CBN | CBV

public export
data Closure = MkClosure Env Tm

covering
Show Closure where
  show (MkClosure xs t) = "(%cl [\{show $ length xs} env] \{show t})"
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
data MetaKind = Normal | User | AutoSolve

public export
Show MetaKind where
  show Normal = "Normal"
  show User = "User"
  show AutoSolve = "Auto"

-- constrain meta applied to val to be a val
public export
data MConstraint = MkMc FC Env (SnocList Val) Val

public export
data MetaEntry = Unsolved FC Nat Context Val MetaKind (List MConstraint) | Solved FC Nat Val


public export
record MetaContext where
  constructor MC
  metas : List MetaEntry
  next : Nat


public export
data Def = Axiom | TCon (List String) | DCon Nat String | Fn Tm | PrimTCon
         | PrimFn String (List String)

public export
covering
Show Def where
  show Axiom = "axiom"
  show (TCon strs) = "TCon \{show strs}"
  show (DCon k tyname) = "DCon \{show k} \{show tyname}"
  show (Fn t) = "Fn \{show t}"
  show (PrimTCon) = "PrimTCon"
  show (PrimFn src uses) = "PrimFn \{show src} \{show uses}"

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
  errors : IORef (List Error)
  ||| loaded modules
  loaded : List String
  ops : Operators

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

  -- FC to use if we don't have a better option
  fc : FC

%name Context ctx

||| add a binding to environment
export
extend : Context -> String -> Val -> Context
extend ctx name ty =
    { lvl $= S, env $= (VVar emptyFC ctx.lvl [<] ::), types $= ((name, ty) ::), bds $= (Bound ::) } ctx

-- I guess we define things as values?
export
define : Context -> String -> Val -> Val -> Context
define ctx name val ty =
  { lvl $= S, env $= (val ::), types $= ((name,ty) ::), bds $= (Defined ::) } ctx


export
covering
Show MetaEntry where
  show (Unsolved pos k ctx ty kind constraints) = "Unsolved \{show pos} \{show k} \{show kind} : \{show ty} \{show ctx.bds} cs \{show $ length constraints}"
  show (Solved _ k x) = "Solved \{show k} \{show x}"

export withPos : Context -> FC -> Context
withPos ctx fc = { fc := fc } ctx

export
names : Context -> List String
names ctx = toList $ map fst ctx.types

public export
M : Type -> Type
M = (StateT TopContext (EitherT Error IO))

||| Force argument and print if verbose is true
export
debug : Lazy String -> M ()
debug x = do
  top <- get
  when top.verbose $ putStrLn x

export
info : FC -> String -> M ()
info fc msg = putStrLn "INFO at \{show fc}: \{msg}"

||| Version of debug that makes monadic computation lazy
export
debugM : M String -> M ()
debugM x = do
  top <- get
  when top.verbose $ do putStrLn !(x)

export partial
Show Context where
  show ctx = "Context \{show $ map fst $ ctx.types}"

export
errorMsg : Error -> String
errorMsg (E x str) = str
errorMsg (Postpone x k str) = str

export
HasFC Error where
  getFC (E x str) = x
  getFC (Postpone x k str) = x

export
error : FC -> String -> M a
error fc msg = throwError $ E fc msg

export
error' : String -> M a
error' msg = throwError $ E emptyFC msg

export
freshMeta : Context -> FC -> Val -> MetaKind -> M Tm
freshMeta ctx fc ty kind = do
  top <- get
  mc <- readIORef top.metas
  debug "fresh meta \{show mc.next} : \{show ty} (\{show kind})"
  writeIORef top.metas $ { next $= S, metas $= (Unsolved fc mc.next ctx ty kind [] ::) } mc
  pure $ applyBDs 0 (Meta fc mc.next) ctx.bds
  where
    -- hope I got the right order here :)
    applyBDs : Nat -> Tm -> Vect k BD -> Tm
    applyBDs k t [] = t
    -- review the order here
    applyBDs k t (Bound :: xs) = App emptyFC (applyBDs (S k) t xs) (Bnd emptyFC k)
    applyBDs k t (Defined :: xs) = applyBDs (S k) t xs

export
lookupMeta : Nat -> M MetaEntry
lookupMeta ix = do
  ctx <- get
  mc <- readIORef ctx.metas
  go mc.metas
  where
    go : List MetaEntry -> M MetaEntry
    go [] = error' "Meta \{show ix} not found"
    go (meta@(Unsolved _ k ys _ _ _) :: xs) = if k == ix then pure meta else go xs
    go (meta@(Solved _ k x) :: xs) = if k == ix then pure meta else go xs

-- we need more of topcontext later - Maybe switch it up so we're not passing
-- around top
export
mkCtx : FC -> Context
mkCtx fc = MkCtx 0 [] [] [] fc

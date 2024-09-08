-- I'm not sure this is related, or just a note to self (Presheaves on Porpoise)

-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

-- ***
-- Kovacs has icity on App, and passes it around, but I'm not sure where it is needed since the insertion happens based on Raw.

module Lib.TT
-- For FC
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types
import Control.Monad.Error.Interface

import Data.IORef
import Data.Fin
import Data.List
import Data.Vect
import Data.SortedMap

-- Errors cribbed from pi-forall
public export
data ErrorSeg : Type where
  DD : Pretty a => a -> ErrorSeg
  DS : String -> ErrorSeg

toDoc : ErrorSeg -> Doc
toDoc (DD x) = pretty x
toDoc (DS str) = text str

export
error : FC -> String -> M a
error fc msg = throwError $ E fc msg

export
error' : String -> M a
error' msg = throwError $ E (0,0) msg

-- order does indeed matter on the meta arguments
-- because of dependent types (if we want something well-typed back out)

export
freshMeta : Context -> FC -> M Tm
freshMeta ctx fc = do
  mc <- readIORef ctx.metas
  putStrLn "INFO at \{show fc}: fresh meta \{show mc.next}"
  writeIORef ctx.metas $ { next $= S, metas $= (Unsolved fc mc.next ctx.bds ::) } mc
  pure $ applyBDs 0 (Meta emptyFC mc.next) ctx.bds
  where
  -- hope I got the right order here :)
  applyBDs : Nat -> Tm -> List BD -> Tm
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
    go (meta@(Unsolved _ k ys) :: xs) = if k == ix then pure meta else go xs
    go (meta@(Solved k x) :: xs) = if k == ix then pure meta else go xs

export partial
Show Context where
  show ctx = "Context \{show $ map fst $ ctx.types}"

-- TODO Pretty Context


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


-- not used
lookup : Context -> String -> M Val
lookup ctx nm = go ctx.types
  where
    go : Vect n (String,Val) -> M Val
    go [] = error' "Name \{nm} not in scope"
    go ((n, ty) :: xs) = if n == nm then pure ty else go xs


-- Need to wire in the metas...
-- if it's top / ctx / IORef, I also need IO...
-- if I want errors, I need m anyway.  I've already got an error down there.

export
eval : Env -> Mode -> Tm -> M Val

-- REVIEW everything is evalutated whether it's needed or not
-- It would be nice if the environment were lazy.
-- e.g. case is getting evaluated when passed to a function because
-- of dependencies in pi-types, even if the dependency isn't used
public export
($$) : {auto mode : Mode} -> Closure -> Val -> M Val
($$) {mode} (MkClosure env tm) u = eval (u :: env) mode tm

public export
infixl 8 $$

export
vapp : Val -> Val -> M Val
vapp (VLam _ _ t) u = t $$ u
vapp (VVar fc k sp) u = pure $ VVar fc k (sp :< u)
vapp (VRef fc nm def sp) u = pure $ VRef fc nm def (sp :< u)
vapp (VMeta fc k sp) u = pure $ VMeta fc k (sp :< u)
vapp t u = error' "impossible in vapp \{show t} to \{show u}"

export
vappSpine : Val -> SnocList Val -> M Val
vappSpine t [<] = pure t
vappSpine t (xs :< x) = vapp !(vappSpine t xs) x

-- So we need:
-- - a Neutral case statement
-- - split out data / type constructors from VRef application
-- - should we sort out what the case tree really looks like first?

-- Technically I don't need this now, as a neutral would be fine.

evalAlt : Env -> Mode -> Val -> List CaseAlt -> M (Maybe Val)
-- FIXME spine length? Should this be VRef or do we specialize?
evalAlt env mode (VRef _ nm y sp) ((CaseCons name args t) :: xs) =
  if nm == name
    -- Here we bind the args and push on. Do we have enough? Too many?
    then ?evalAlt_success
    -- here we need to know if we've got a mismatched constructor or some function app
    else ?evalAlt_what
evalAlt env mode sc (CaseDefault u :: xs) = pure $ Just !(eval (sc :: env) mode u)
evalAlt env mode sc _ = pure Nothing -- stuck

bind : Val -> Env -> Env
bind v env = v :: env

-- So smalltt says:
--   Smalltt has the following approach:
--   - Top-level and local definitions are lazy.
--   - We instantiate Pi types during elaboration with lazy values.
--   - Applications headed by top-level variables are lazy.
--   - Any other function application is call-by-value during evaluation.

-- Do we want a def in here instead?  We'll need DCon/TCon eventually
-- I need to be aggressive about reduction, I guess. I'll figure it out
-- later, maybe need lazy glued values.
-- TODO - probably want to figure out gluing and handle constructors
eval env mode (Ref _ x (Fn tm)) = eval env mode tm
eval env mode (Ref fc x def) = pure $ VRef fc x def [<]
eval env mode (App _ t u) = vapp !(eval env mode t) !(eval env mode u)
eval env mode (U fc) = pure (VU fc)
eval env mode (Meta fc i) =
  case !(lookupMeta i) of
        (Unsolved _ k xs) => pure $ VMeta fc i [<]
        (Solved k t) => pure $ t
eval env mode (Lam fc x t) = pure $ VLam fc x (MkClosure env t)
eval env mode (Pi fc x icit a b) = pure $ VPi fc x icit !(eval env mode a) (MkClosure env b)
eval env mode (Let fc nm t u) = pure $ VLet fc nm !(eval env mode t) (MkClosure env u)
-- Here, we assume env has everything. We push levels onto it during type checking.
-- I think we could pass in an l and assume everything outside env is free and
-- translate to a level
eval env mode (Bnd fc i) = case getAt i env of
  Just rval => pure rval
  Nothing => error' "Bad deBruin index \{show i}"
eval env mode (Lit fc lit) = pure $ VLit fc lit

-- We need a neutral and some code to run the case tree

eval env mode tm@(Case fc sc alts) = pure $ VCase fc !(eval env mode sc) alts
  -- case !(evalAlt env mode !(eval env mode sc) alts) of
  --   Just foo => ?goodAlt
  --   Nothing => ?stuckAlt

export
quote : (lvl : Nat) -> Val -> M Tm


quoteSp : (lvl : Nat) -> Tm -> SnocList Val -> M Tm
quoteSp lvl t [<] = pure t
quoteSp lvl t (xs :< x) =
  pure $ App emptyFC !(quoteSp lvl t xs) !(quote lvl x)
  -- quoteSp lvl (App t !(quote lvl x)) xs  -- snoc says previous is right

quote l (VVar fc k sp) = if k < l
  then quoteSp l (Bnd emptyFC ((l `minus` k) `minus` 1)) sp -- level to index
  else ?borken
quote l (VMeta fc i sp) = quoteSp l (Meta fc i) sp
quote l (VLam fc x t) = pure $ Lam fc x !(quote (S l) !(t $$ VVar emptyFC l [<]))
quote l (VPi fc x icit a b) = pure $ Pi fc x icit !(quote l a) !(quote (S l) !(b $$ VVar emptyFC l [<]))
quote l (VLet fc nm t u) = pure $ Let fc nm !(quote l t) !(quote (S l) !(u $$ VVar emptyFC l [<]))
quote l (VU fc) = pure (U fc)
quote l (VRef fc n def sp) = quoteSp l (Ref fc n def) sp
quote l (VCase fc sc alts) = pure $ Case fc !(quote l sc) alts
quote l (VLit fc lit) = pure $ Lit fc lit

-- Can we assume closed terms?
-- ezoo only seems to use it at [], but essentially does this:
export
nf : Env -> Tm -> M Tm
nf env t = quote (length env) !(eval env CBN t)

export
prval : Val -> M String
prval v = pure $ pprint [] !(quote 0 v)

export
prvalCtx : {auto ctx : Context} -> Val -> M String
prvalCtx v = pure $ pprint (toList $ map fst ctx.types) !(quote ctx.lvl v)


export
solveMeta : TopContext -> Nat -> Val -> M ()
solveMeta ctx ix tm = do
  mc <- readIORef ctx.metas
  metas <- go mc.metas [<]
  writeIORef ctx.metas $ {metas := metas} mc
  where
    go : List MetaEntry -> SnocList MetaEntry -> M (List MetaEntry)
    go [] _ = error' "Meta \{show ix} not found"
    go (meta@(Unsolved pos k _) :: xs) lhs = if k == ix
      then do
        -- empty context should be ok, because this needs to be closed
        putStrLn "INFO at \{show pos}: solve \{show k} as \{!(prval tm)}"
        pure $ lhs <>> (Solved k tm :: xs)
      else go xs (lhs :< meta)
    go (meta@(Solved k _) :: xs) lhs = if k == ix
      then error' "Meta \{show ix} already solved!"
      else go xs (lhs :< meta)


-- REVIEW - might be easier if we inserted the meta without a bunch of explicit App

-- we need to walk the whole thing
-- meta in Tm have a bunch of args, which should be the relevant
-- parts of the scope. So, meta has a bunch of lambdas, we've got a bunch of
-- args and we need to beta reduce, which seems like a lot of work for nothing
-- Could we put the "good bits" of the Meta in there and write it to Bnd directly
-- off of scope? I guess this might get dicey when a meta is another meta applied
-- to something.

-- ok, so we're doing something that looks lot like eval, having to collect args,
-- pull the def, and apply spine. Eval is trying for WHNF, so it doesn't walk the
-- whole thing. (We'd like to insert metas inside lambdas.)
export
zonk : TopContext -> Nat -> Env -> Tm -> M Tm

zonkBind : TopContext -> Nat -> Env -> Tm -> M Tm
zonkBind top l env tm = zonk top (S l) (VVar (getFC tm) l [<] :: env) tm

-- I don't know if app needs an FC...

appSpine : Tm -> List Tm -> Tm
appSpine t [] = t
appSpine t (x :: xs) = appSpine (App (getFC t) t x) xs

zonkApp : TopContext -> Nat -> Env -> Tm -> List Tm -> M Tm
zonkApp top l env (App fc t u) sp = zonkApp top l env t (!(zonk top l env u) :: sp)
zonkApp top l env t@(Meta fc k) sp = case !(lookupMeta k) of
  (Solved j v) => do
    sp' <- traverse (eval env CBN) sp
    debug "zonk \{show k} -> \{show v} spine \{show sp'}"
    foo <- vappSpine v ([<] <>< sp')
    debug "-> result is \{show foo}"
    quote l foo
  (Unsolved x j xs) => pure $ appSpine t sp
zonkApp top l env t sp = pure $ appSpine !(zonk top l env t) sp

zonkAlt : TopContext -> Nat -> Env -> CaseAlt -> M CaseAlt
zonkAlt top l env (CaseDefault t) = CaseDefault <$> zonkBind top l env t
zonkAlt top l env (CaseCons name args t) = CaseCons name args <$> go l env args t
  where
    go : Nat -> Env -> List String -> Tm -> M Tm
    go l env [] tm = zonk top l env t
    go l env (x :: xs) tm = go (S l) (VVar (getFC tm) l [<] :: env) xs tm

zonk top l env t = case t of
  (Meta fc k) => zonkApp top l env t []
  (Lam fc nm u) => Lam fc nm <$> (zonk top (S l) (VVar fc l [<] :: env) u)
  (App fc t u) => zonkApp top l env t [!(zonk top l env u)]
  (Pi fc nm icit a b) => Pi fc nm icit <$> zonk top l env a <*> zonkBind top l env b
  (Let fc nm t u) => Let fc nm <$> zonk top l env t <*> zonkBind top l env u
  (Case fc sc alts) => Case fc <$> zonk top l env sc <*> traverse (zonkAlt top l env) alts
  _ => pure t

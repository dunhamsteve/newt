module Lib.Eval

-- For FC
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types
import Control.Monad.Error.Interface

import Data.IORef
import Data.Fin
import Data.List
import Data.SnocList
import Data.Vect
import Data.SortedMap

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

evalCase : Env -> Mode -> Val -> List CaseAlt -> M (Maybe Val)
evalCase env mode sc@(VRef _ nm y sp) (cc@(CaseCons name nms t) :: xs) =
  if nm == name
    then go env sp nms
    else evalCase env mode sc xs
  where
    go : Env -> SnocList Val -> List String -> M (Maybe Val)
    go env (args :< arg) (nm :: nms) = go (arg :: env) args nms
    go env args [] = Just <$> vappSpine !(eval env mode t) args
    go env [<] rest = pure Nothing

evalCase env mode sc (CaseDefault u :: xs) = pure $ Just !(eval (sc :: env) mode u)
evalCase env mode sc _ = pure Nothing

bind : Val -> Env -> Env
bind v env = v :: env

-- So smalltt says:
--   Smalltt has the following approach:
--   - Top-level and local definitions are lazy.
--   - We instantiate Pi types during elaboration with lazy values.
--   - Applications headed by top-level variables are lazy.
--   - Any other function application is call-by-value during evaluation.

-- TODO - probably want to figure out gluing and handle constructors
eval env mode (Ref _ x (Fn tm)) = eval env mode tm
eval env mode (Ref fc x def) = pure $ VRef fc x def [<]
eval env mode (App _ t u) = vapp !(eval env mode t) !(eval env mode u)
eval env mode (U fc) = pure (VU fc)
eval env mode (Meta fc i) =
  case !(lookupMeta i) of
        (Unsolved _ k xs _) => pure $ VMeta fc i [<]
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

eval env mode tm@(Case fc sc alts) =
  case !(evalCase env mode !(eval env mode sc) alts) of
    Just v => pure v
    Nothing => pure $ fromMaybe (VCase fc !(eval env mode sc) alts)
                                !(evalCase env mode !(eval env mode sc) alts)

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
quote l (VMeta fc i sp) =
  case !(lookupMeta i) of
        (Unsolved _ k xs _) => quoteSp l (Meta fc i) sp
        (Solved k t) => quote l !(vappSpine t sp)
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
    go (meta@(Unsolved pos k _ _) :: xs) lhs = if k == ix
      then do
        -- empty context should be ok, because this needs to be closed
        putStrLn "INFO at \{show pos}: solve \{show k} as \{!(prval tm)}"
        pure $ lhs <>> (Solved k tm :: xs)
      else go xs (lhs :< meta)
    go (meta@(Solved k _) :: xs) lhs = if k == ix
      then error' "Meta \{show ix} already solved!"
      else go xs (lhs :< meta)


-- REVIEW - might be easier if we inserted the meta without a bunch of explicit App
-- I believe Kovacs is doing that.

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
  (Unsolved x j xs _) => pure $ appSpine t sp
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

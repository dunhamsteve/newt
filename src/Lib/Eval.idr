module Lib.Eval

import Lib.Types
import Lib.TopContext

import Data.IORef
import Data.Fin
import Data.List
import Data.SnocList
import Data.Vect
import Data.SortedMap

export
eval : Env -> Mode -> Tm -> M Val

-- REVIEW everything is evalutated whether it's needed or not
-- It would be nice if the environment were lazy.
-- e.g. case is getting evaluated when passed to a function because
-- of dependencies in pi-types, even if the dependency isn't used

public export
infixl 8 $$

public export
($$) : {auto mode : Mode} -> Closure -> Val -> M Val
($$) {mode} (MkClosure env tm) u = eval (u :: env) mode tm

export
vapp : Val -> Val -> M Val
vapp (VLam _ _ _ _ t) u = t $$ u
vapp (VVar fc k sp) u = pure $ VVar fc k (sp :< u)
vapp (VRef fc nm def sp) u = pure $ VRef fc nm def (sp :< u)
vapp (VMeta fc k sp) u = pure $ VMeta fc k (sp :< u)
vapp t u = error' "impossible in vapp \{show t} to \{show u}\n"

export
vappSpine : Val -> SnocList Val -> M Val
vappSpine t [<] = pure t
vappSpine t (xs :< x) = do
  rest <- vappSpine t xs
  vapp rest x

lookupVar : Env -> Nat -> Maybe Val
lookupVar env k = let l = length env in
  if k > l
    then Nothing
    else case getAt (lvl2ix l k) env of
      Just v@(VVar fc k' sp) => if k == k' then Nothing else Just v
      Just v => Just v
      Nothing => Nothing

-- hoping to apply what we got via pattern matching
export
unlet : Env -> Val -> M Val
unlet env t@(VVar fc k sp) = case lookupVar env k of
      Just tt@(VVar fc' k' sp') => do
        debug "lookup \{show k} is \{show tt}"
        if k' == k then pure t else (vappSpine (VVar fc' k' sp') sp >>= unlet env)
      Just t => vappSpine t sp >>= unlet env
      Nothing => do
        debug "lookup \{show k} is Nothing in env \{show env}"
        pure t
unlet env x = pure x

export
tryEval : Env -> Val -> M (Maybe Val)
tryEval env (VRef fc k _ sp) = do
  top <- get
  case lookup k top of
      Just (MkEntry _ name ty (Fn tm)) =>
        catchError (
            do
            debug "app \{show name} to \{show sp}"
            vtm <- eval [] CBN tm
            debug "tm is \{render 90 $ pprint [] tm}"
            val <- vappSpine vtm sp
            case val of
              VCase _ _ _ => pure Nothing
              VLetRec _ _ _ _ _ => pure Nothing
              v => pure $ Just v)
            (\ _ => pure Nothing)
      _ => pure Nothing
tryEval _ _ = pure Nothing

-- Force far enough to compare types
export
forceType : Env -> Val -> M Val
forceType env (VMeta fc ix sp) = do
  meta <- lookupMeta ix
  case meta of
    (Unsolved x k xs _ _ _) => pure (VMeta fc ix sp)
    (Solved _ k t) => vappSpine t sp >>= forceType env
forceType env x = do
  Just x' <- tryEval env x
    | _ => pure x
  forceType env x'

evalCase : Env -> Mode -> Val -> List CaseAlt -> M (Maybe Val)
evalCase env mode sc@(VRef _ nm _ sp) (cc@(CaseCons name nms t) :: xs) = do
  top <- get
  if nm == name
    then do
      debug "ECase \{show nm} \{show sp} \{show nms} \{showTm t}"
      go env (sp <>> []) nms
    else case lookup nm top of
      (Just (MkEntry _ str type (DCon k str1))) => evalCase env mode sc xs
      -- bail for a stuck function
      _ => pure Nothing
  where
    go : Env -> List Val -> List String -> M (Maybe Val)
    go env (arg :: args) (nm :: nms) = go (arg :: env) args nms
    go env args [] = do
      t' <- eval env mode t
      Just <$> vappSpine t' ([<] <>< args)
    go env [] rest = pure Nothing
-- REVIEW - this is handled in the caller already
evalCase env mode sc@(VVar fc k sp) alts = case lookupVar env k of
    Just tt@(VVar fc' k' sp') => do
        debug "lookup \{show k} is \{show tt}"
        if k' == k
          then pure Nothing
          else do
            val <- vappSpine (VVar fc' k' sp') sp
            evalCase env mode val alts
    Just t => do
      val <- vappSpine t sp
      evalCase env mode val alts
    Nothing => do
        debug "lookup \{show k} is Nothing in env \{show env}"
        pure Nothing
evalCase env mode sc (CaseDefault u :: xs) = Just <$> eval (sc :: env) mode u
evalCase env mode sc cc = do
  debug "CASE BAIL sc \{show sc} vs \{show cc}"
  debug "env is \{show env}"
  pure Nothing

-- TODO maybe add glueing

eval env mode (Ref fc x def) = pure $ VRef fc x def [<]
eval env mode (App _ t u) = do
  t' <- eval env mode t
  u' <- eval env mode u
  vapp t' u'
eval env mode (UU fc) = pure (VU fc)
eval env mode (Erased fc) = pure (VErased fc)
eval env mode (Meta fc i) = do
  meta <- lookupMeta i
  case meta of
        (Unsolved _ k xs _ _ _) => pure $ VMeta fc i [<]
        (Solved _ k t) => pure $ t
eval env mode (Lam fc x icit rig t) = pure $ VLam fc x icit rig (MkClosure env t)
eval env mode (Pi fc x icit rig a b) = do
  a' <- eval env mode a
  pure $ VPi fc x icit rig a' (MkClosure env b)
eval env mode (Let fc nm t u) = do
  t' <- eval env mode t
  u' <- eval (VVar fc (length env) [<] :: env) mode u
  pure $ VLet fc nm t' u'
eval env mode (LetRec fc nm ty t u) = do
  ty' <- eval env mode ty
  t' <- eval (VVar fc (length env) [<] :: env) mode t
  u' <- eval (VVar fc (length env) [<] :: env) mode u
  pure $ VLetRec fc nm ty' t' u'
-- Here, we assume env has everything. We push levels onto it during type checking.
-- I think we could pass in an l and assume everything outside env is free and
-- translate to a level
eval env mode (Bnd fc i) = case getAt i env of
  Just rval => pure rval
  Nothing => error fc "Bad deBruin index \{show i}"
eval env mode (Lit fc lit) = pure $ VLit fc lit

eval env mode tm@(Case fc sc alts) = do
  -- TODO we need to be able to tell eval to expand aggressively here.
  sc' <- eval env mode sc
  sc' <- unlet env sc' -- try to expand lets from pattern matching
  sc' <- forceType env sc'
  vsc <- eval env mode sc
  vcase <- evalCase env mode sc' alts
  pure $ fromMaybe (VCase fc vsc alts) vcase

export
quote : (lvl : Nat) -> Val -> M Tm

quoteSp : (lvl : Nat) -> Tm -> SnocList Val -> M Tm
quoteSp lvl t [<] = pure t
quoteSp lvl t (xs :< x) = do
  t' <- quoteSp lvl t xs
  x' <- quote lvl x
  pure $ App emptyFC t' x'

quote l (VVar fc k sp) = if k < l
  then quoteSp l (Bnd fc (lvl2ix l k )) sp -- level to index
  else error fc "Bad index in quote \{show k} depth \{show l}"
quote l (VMeta fc i sp) = do
  meta <- lookupMeta i
  case meta of
        (Unsolved _ k xs _ _ _) => quoteSp l (Meta fc i) sp
        (Solved _ k t) => vappSpine t sp >>= quote l
quote l (VLam fc x icit rig t) = do
  val <- t $$ VVar emptyFC l [<]
  tm <- quote (S l) val
  pure $ Lam fc x icit rig tm
quote l (VPi fc x icit rig a b) = do
  a' <- quote l a
  val <- b $$ VVar emptyFC l [<]
  tm <- quote (S l) val
  pure $ Pi fc x icit rig a' tm
quote l (VLet fc nm t u) = do
  t' <- quote l t
  u' <- quote (S l) u
  pure $ Let fc nm t' u'
quote l (VLetRec fc nm ty t u) = do
  ty' <- quote l ty
  t' <- quote (S l) t
  u' <- quote (S l) u
  pure $ LetRec fc nm ty' t' u'
quote l (VU fc) = pure (UU fc)
quote l (VRef fc n def sp) = quoteSp l (Ref fc n def) sp
quote l (VCase fc sc alts) = do
  sc' <- quote l sc
  pure $ Case fc sc' alts
quote l (VLit fc lit) = pure $ Lit fc lit
quote l (VErased fc) = pure $ Erased fc

-- Can we assume closed terms?
-- ezoo only seems to use it at [], but essentially does this:
export
nf : Env -> Tm -> M Tm
nf env t = eval env CBN t >>= quote (length env)

export
nfv : Env -> Tm -> M Tm
nfv env t = eval env CBV t >>= quote (length env)

export
prvalCtx : {auto ctx : Context} -> Val -> M String
prvalCtx v = do
  tm <- quote ctx.lvl v
  pure $ interpolate $ pprint (toList $ map fst ctx.types) tm

export
zonk : TopContext -> Nat -> Env -> Tm -> M Tm

zonkBind : TopContext -> Nat -> Env -> Tm -> M Tm
zonkBind top l env tm = zonk top (S l) (VVar (getFC tm) l [<] :: env) tm

-- I don't know if app needs an FC...

appSpine : Tm -> List Tm -> Tm
appSpine t [] = t
appSpine t (x :: xs) = appSpine (App (getFC t) t x) xs

-- REVIEW When metas are subst in, the fc point elsewhere
-- We might want to update when it is solved and update recursively?
-- For errors, I think we want to pretend the code has been typed in place
tweakFC : FC -> Tm -> Tm
tweakFC fc (Bnd fc1 k) = Bnd fc k
tweakFC fc (Ref fc1 nm x) = Ref fc nm x
tweakFC fc (UU fc1) = UU fc
tweakFC fc (Meta fc1 k) = Meta fc k
tweakFC fc (Lam fc1 nm icit rig t) = Lam fc nm icit rig t
tweakFC fc (App fc1 t u) = App fc t u
tweakFC fc (Pi fc1 nm icit x t u) = Pi fc nm icit x t u
tweakFC fc (Case fc1 t xs) = Case fc t xs
tweakFC fc (Let fc1 nm t u) = Let fc nm t u
tweakFC fc (LetRec fc1 nm ty t u) = LetRec fc nm ty t u
tweakFC fc (Lit fc1 lit) = Lit fc lit
tweakFC fc (Erased fc1) = Erased fc

-- TODO replace this with a variant on nf
zonkApp : TopContext -> Nat -> Env -> Tm -> List Tm -> M Tm
zonkApp top l env (App fc t u) sp = do
  u' <- zonk top l env u
  zonkApp top l env t (u' :: sp)
zonkApp top l env t@(Meta fc k) sp = do
  meta <- lookupMeta k
  case meta of
    (Solved _ j v) => do
      sp' <- traverse (eval env CBN) sp
      debug "zonk \{show k} -> \{show v} spine \{show sp'}"
      foo <- vappSpine v ([<] <>< sp')
      debug "-> result is \{show foo}"
      tweakFC fc <$> quote l foo
    (Unsolved x j xs _ _ _) => pure $ appSpine t sp
zonkApp top l env t sp = do
  t' <- zonk top l env t
  pure $ appSpine t' sp

zonkAlt : TopContext -> Nat -> Env -> CaseAlt -> M CaseAlt
zonkAlt top l env (CaseDefault t) = CaseDefault <$> zonkBind top l env t
zonkAlt top l env (CaseLit lit t) = CaseLit lit <$> zonkBind top l env t
zonkAlt top l env (CaseCons name args t) = CaseCons name args <$> go l env args t
  where
    go : Nat -> Env -> List String -> Tm -> M Tm
    go l env [] tm = zonk top l env t
    go l env (x :: xs) tm = go (S l) (VVar (getFC tm) l [<] :: env) xs tm

zonk top l env t = case t of
  (Meta fc k) => zonkApp top l env t []
  (Lam fc nm icit rig u) => Lam fc nm icit rig <$> (zonk top (S l) (VVar fc l [<] :: env) u)
  (App fc t u) => do
    u' <- zonk top l env u
    zonkApp top l env t [u']
  (Pi fc nm icit rig a b) => Pi fc nm icit rig <$> zonk top l env a <*> zonkBind top l env b
  (Let fc nm t u) => Let fc nm <$> zonk top l env t <*> zonkBind top l env u
  (LetRec fc nm ty t u) => LetRec fc nm <$> zonk top l env ty <*> zonkBind top l env t <*> zonkBind top l env u
  (Case fc sc alts) => Case fc <$> zonk top l env sc <*> traverse (zonkAlt top l env) alts
  UU fc => pure $ UU fc
  Lit fc lit => pure $ Lit fc lit
  Bnd fc ix => pure $ Bnd fc ix
  Ref fc ix def => pure $ Ref fc ix def
  Erased fc => pure $ Erased fc

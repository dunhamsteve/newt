module Lib.Erasure

import Lib.Types
import Data.Maybe
import Data.SnocList
import Lib.TopContext

EEnv = List (String, Quant, Maybe Tm)

-- TODO look into removing Nothing below, can we recover all of the types?
-- Idris does this in `chk` for linearity checking.

-- check App at type

getType : Tm -> M (Maybe Tm)
getType (Ref fc nm x) = do
  top <- get
  case lookup nm top of
    Nothing => error fc "\{nm} not in scope"
    (Just (MkEntry _ name type def)) => pure $ Just type
getType tm = pure Nothing

export
erase : EEnv -> Tm -> List (FC, Tm) -> M Tm

-- App a spine using type
eraseSpine : EEnv -> Tm -> List (FC, Tm) -> (ty : Maybe Tm) -> M Tm
eraseSpine env tm [] _ = pure tm
eraseSpine env t ((fc, arg) :: args) (Just (Pi fc1 str icit Zero a b)) = do
  let u = Erased (getFC arg)
  eraseSpine env (App fc t u) args (Just b)
eraseSpine env t ((fc, arg) :: args) (Just (Pi fc1 str icit Many a b)) = do
  u <- erase env arg []
  -- TODO this seems wrong, we need to subst u into b to get the type
  eraseSpine env (App fc t u) args (Just b)
-- eraseSpine env t ((fc, arg) :: args) (Just ty) = do
--   error fc "ceci n'est pas une ∏ \{showTm ty}" -- e.g. Bnd 1
eraseSpine env t ((fc, arg) :: args) _ = do
  u <- erase env arg []
  eraseSpine env (App fc t u) args Nothing

doAlt : EEnv -> CaseAlt -> M CaseAlt
-- REVIEW do we extend env?
doAlt env (CaseDefault t) = CaseDefault <$> erase env t []
doAlt env (CaseCons name args t) = do
  top <- get
  let Just (MkEntry _ str type def) = lookup name top
    | _ => error emptyFC "\{name} dcon missing from context"
  let env' = piEnv env type args
  CaseCons name args <$> erase env' t []
  where
    piEnv : EEnv -> Tm -> List String -> EEnv
    piEnv env (Pi fc nm icit rig t u) (arg :: args) = piEnv ((arg, rig, Just t) :: env) u args
    piEnv env _ _ = env

doAlt env (CaseLit lit t) = CaseLit lit <$> erase env t []

-- Check erasure and insert "Erased" value
-- We have a solution for Erased values, so important thing here is checking.
-- build stack, see what to do when we hit a non-app
-- This is a little fuzzy because we don't have all of the types.
erase env t sp = case t of
  (App fc u v) => erase env u ((fc,v) :: sp)
  (Ref fc nm x) => do
    top <- get
    case lookup nm top of
      Nothing => error fc "\{nm} not in scope"
      (Just (MkEntry _ name type def)) => eraseSpine env t sp (Just type)
  (Lam fc nm icit rig u) => Lam fc nm icit rig <$> erase ((nm, rig, Nothing) :: env) u []
  -- If we get here, we're looking at a runtime pi type
  (Pi fc nm icit rig u v) => do
    u' <- erase env u []
    v' <- erase ((nm, Many, Just u) :: env) v []
    eraseSpine env (Pi fc nm icit rig u' v') sp (Just $ UU emptyFC)
  -- leaving as-is for now, we don't know the quantity of the apps
  (Meta fc k) => pure t
  (Case fc u alts) => do
    -- REVIEW check if this pushes to env, and write that down or get an index on there
    u' <- erase env u []
    alts' <- traverse (doAlt env) alts
    eraseSpine env (Case fc u' alts') sp Nothing
  (Let fc nm u v) => do
    u' <- erase env u []
    v' <- erase ((nm, Many, Nothing) :: env) v []
    eraseSpine env (Let fc nm u' v') sp Nothing
  (LetRec fc nm ty u v) => do
    u' <- erase ((nm, Many, Just ty) :: env) u []
    v' <- erase ((nm, Many, Just ty) :: env) v []
    eraseSpine env (LetRec fc nm ty u' v') sp Nothing
  (Bnd fc k) => do
    case getAt k env of
      Nothing => error fc "bad index \{show k}"
      -- This is working, but empty FC
      Just (nm, Zero, ty) => error fc "used erased value \{show nm} (FIXME FC may be wrong here)"
      Just (nm, Many, ty) => eraseSpine env t sp ty
  (UU fc) => eraseSpine env t sp (Just $ UU fc)
  (Lit fc lit) => eraseSpine env t sp Nothing
  Erased fc => error fc "erased value in relevant context" -- eraseSpine env t sp Nothing



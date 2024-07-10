module Lib.Check

import Control.Monad.Error.Interface
import Control.Monad.Identity
import Lib.Parser.Impl
import Lib.Prettier
import Data.List
import Data.Vect
import Data.String
import Lib.Types
import Lib.TT
import Lib.TopContext
import Syntax

-- renaming
-- dom gamma ren
data PRen = PR Nat Nat (List Nat)

-- IORef for metas needs IO

forceMeta : Val -> M Val
-- TODO - need to look up metas
forceMeta (VMeta ix sp) = case !(lookupMeta ix) of
  (Unsolved k xs) => pure (VMeta ix sp)
  (Solved k t) => vappSpine t sp
forceMeta x = pure x

-- return renaming, the position is the new VVar
invert : Nat -> SnocList Val -> M (List Nat)
invert lvl sp = go sp []
  where
    go : SnocList Val -> List Nat -> M (List Nat)
    go [<] acc = pure $ reverse acc
    go (xs :< VVar k [<]) acc = do
      if elem k acc 
        then throwError $ E (0,0) "non-linear pattern"
        else go xs (k :: acc)
    go _ _ = throwError $ E (0,0) "non-variable in pattern"

-- we have to "lift" the renaming when we go under a lambda
-- I think that essentially means our domain ix are one bigger, since we're looking at lvl
-- in the codomain, so maybe we can just keep that value
rename : Nat ->  List Nat -> Nat -> Val  -> M  Tm
rename meta ren lvl v = go ren lvl v
  where
    go : List Nat -> Nat -> Val  -> M  Tm
    goSpine : List Nat -> Nat -> Tm -> SnocList Val  -> M  Tm
    goSpine ren lvl tm [<] = pure tm
    goSpine ren lvl tm (xs :< x) = do
      xtm <- go ren lvl x
      goSpine ren lvl (App tm xtm) xs

    go ren lvl (VVar k sp) = case findIndex (== k) ren of
      Nothing => throwError $ E (0,0) "scope/skolem thinger"
      Just x => goSpine ren lvl (Bnd $ cast x) sp
    go ren lvl (VRef nm sp) = goSpine ren lvl (Ref nm Nothing) sp
    go ren lvl (VMeta ix sp) = if ix == meta
      then throwError $ E (0,0) "meta occurs check"
      else goSpine ren lvl (Meta ix) sp
    go ren lvl (VLam n icit t) = pure (Lam n icit !(go (lvl :: ren) (S lvl) !(t $$ VVar lvl [<])))
    go ren lvl (VPi n icit ty tm) = pure (Pi n icit !(go ren lvl ty) !(go (lvl :: ren) (S lvl) !(tm $$ VVar lvl [<])))
    go ren lvl VU = pure U

lams : Nat -> Tm -> Tm
lams 0 tm = tm
lams (S k) tm = Lam "arg\{show k}" Explicit (lams k tm)

solve : Nat -> Nat -> SnocList Val -> Val  -> M  ()
solve l m sp t = do
  ren <- invert l sp
  tm <- rename m ren l t
  let tm = lams (length sp) tm
  top <- get
  soln <- eval [] CBN tm
  solveMeta top m soln
  pure ()

unify : (l : Nat) -> Val -> Val  -> M  ()

unifySpine : Nat -> Bool -> SnocList Val -> SnocList Val  -> M  ()
unifySpine l False _ _ = throwError $ E (0,0) "unify failed"
unifySpine l True [<] [<] = pure ()
unifySpine l True (xs :< x) (ys :< y) = unify l x y >> unifySpine l True xs ys
unifySpine l True _ _ = throwError $ E (0,0) "meta spine length mismatch"

unify l t u = do
  t' <- forceMeta t
  u' <- forceMeta u
  case (t',u') of
    (VLam _ _ t,  VLam _ _ t'  ) => unify (l + 1) !(t $$ VVar l [<]) !(t' $$ VVar l [<])
    (t,           VLam _ _ t'  ) => unify (l + 1) !(t `vapp` VVar l [<]) !(t' $$ VVar l [<])
    (VLam _ _ t,  t'           ) => unify (l + 1) !(t $$ VVar l [<]) !(t' `vapp` VVar l [<])
    (VPi _ _ a b, VPi _ _ a' b') => unify l a a' >> unify (S l) !(b $$ VVar l [<]) !(b' $$ VVar l [<])
    (VVar k sp,   VVar k' sp'  ) => unifySpine l (k == k') sp sp'
    (VRef n sp,   VRef n' sp'  ) => unifySpine l (n == n') sp sp'
    (VMeta i sp,  VMeta i' sp' ) => unifySpine l (i == i') sp sp'

    (t,           VMeta i' sp') => solve l i' sp' t
    (VMeta i sp, t'           ) => solve l i sp t'
    (VU, VU) => pure ()
    _ => throwError $ E (0,0) "unify failed"


export
infer : Context -> Raw  -> M  (Tm, Val)

export
check : Context -> Raw -> Val  -> M  Tm
check ctx (RSrcPos x tm) ty = check ({pos := x} ctx) tm ty
check ctx (RLam nm icit tm) ty = case ty of                    
                  (VPi pinm icit a b) => do
                    -- TODO icit
                    let var = VVar (length ctx.env) [<]
                    let ctx' = extend ctx nm a
                    tm' <- check ctx' tm !(b $$ var)
                    pure $ Lam nm icit tm'
                  other => error [(DS "Expected pi type, got \{show !(quote 0 ty)}")]
check ctx tm ty = do
  (tm', ty') <- infer ctx tm
  -- This is where the conversion check / pattern unification go
  unify ctx.lvl ty' ty
  -- if quote 0 ty /= quote 0 ty' then
  --     error [DS "type mismatch got", DD (quote 0 ty'), DS "expected", DD (quote 0 ty)]
  --   else pure tm'
  pure tm'

infer ctx (RVar nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M  (Tm, Val)
    go i [] = case lookup nm !(get) of
      Just (MkEntry name ty (Fn t)) => pure (Ref nm (Just t), !(eval [] CBN ty))
      Just (MkEntry name ty _) => pure (Ref nm Nothing, !(eval [] CBN ty))
      Nothing => error [DS "\{show nm} not in scope"]
    go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd i, ty) 
      else go (i + 1) xs
  -- need environment of name -> type..
infer ctx (RApp t u icit) = do 
  -- icit will be used for insertion, lets get this working first...
  (t, tty) <- infer ctx t
  case tty of
    (VPi str icit' a b) => do
      u <- check ctx u a
      pure (App t u, !(b $$ !(eval ctx.env CBN u)))
    _ => error [DS "Expected Pi type"]
infer ctx RU = pure (U, VU) -- YOLO
infer ctx (RPi nm icit ty ty2) = do
  ty' <- check ctx ty VU
  vty' <- eval ctx.env CBN ty'
  let nm := fromMaybe "_" nm
  ty2' <- check (extend ctx nm vty') ty2 VU
  pure (Pi nm icit ty' ty2', VU)
infer ctx (RLet str tm tm1 tm2) = error [DS "implement RLet"]
infer ctx (RSrcPos x tm) = infer ({pos := x} ctx) tm
infer ctx (RAnn tm rty) = do
  ty <- check ctx rty VU
  vty <- eval ctx.env CBN ty 
  tm <- check ctx tm vty
  pure (tm, vty)

infer ctx (RLam str icit tm) = error [DS "can't infer lambda"]
infer ctx RHole = do
  ty <- freshMeta ctx
  vty <- eval ctx.env CBN ty
  tm <- freshMeta ctx
  pure (tm, vty)
  
infer ctx tm = error [DS "Implement infer \{show tm}"]

-- I don't have types for these yet...
-- infer ctx (RLit (LString str)) = ?rhs_10
-- infer ctx (RLit (LInt i)) = ?rhs_11
-- infer ctx (RLit (LBool x)) = ?rhs_12
-- infer ctx (RCase tm xs) = ?rhs_9
-- infer ctx RHole = ?todo_meta2
-- The idea here is to insert a hole for a parse error
-- infer ctx (RParseError str) = ?todo_insert_meta

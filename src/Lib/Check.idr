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
  (Unsolved pos k xs) => pure (VMeta ix sp)
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
rename : Nat -> List Nat -> Nat -> Val  -> M  Tm
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
lams (S k) tm = Lam "arg:\{show k}" Explicit (lams k tm)

solve : Nat -> Nat -> SnocList Val -> Val  -> M  ()
solve l m sp t = do
  ren <- invert l sp
  tm <- rename m ren l t
  let tm = lams (length sp) tm
  top <- get
  soln <- eval [] CBN tm
  solveMeta top m soln
  pure ()

parameters (ctx: Context)
  unify : (l : Nat) -> Val -> Val  -> M  ()

  unifySpine : Nat -> Bool -> SnocList Val -> SnocList Val  -> M  ()
  unifySpine l False _ _ = error [DS "unify failed at head"] -- unreachable now
  unifySpine l True [<] [<] = pure ()
  unifySpine l True (xs :< x) (ys :< y) = unify l x y >> unifySpine l True xs ys
  unifySpine l True _ _ = error [DS "meta spine length mismatch"]

  unify l t u = do
    putStrLn "Unify \{show ctx.lvl}"
    putStrLn "  \{show l} \{show t}"
    putStrLn "  =?= \{show u}"
    t' <- forceMeta t
    u' <- forceMeta u
    case (t',u') of
      (VLam _ _ t,  VLam _ _ t'  ) => unify (l + 1) !(t $$ VVar l [<]) !(t' $$ VVar l [<])
      (t,           VLam _ _ t'  ) => unify (l + 1) !(t `vapp` VVar l [<]) !(t' $$ VVar l [<])
      (VLam _ _ t,  t'           ) => unify (l + 1) !(t $$ VVar l [<]) !(t' `vapp` VVar l [<])
      (VPi _ _ a b, VPi _ _ a' b') => unify l a a' >> unify (S l) !(b $$ VVar l [<]) !(b' $$ VVar l [<])
      (VVar k sp,   VVar k' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else error [DS "vvar mismatch \{show k} \{show k'}"]
      (VRef k sp,   VRef k' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else error [DS "vref mismatch \{show k} \{show k'}"]
      (VMeta k sp,  VMeta k' sp' ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else solve l k sp (VMeta k' sp')
      (t,           VMeta i' sp') => solve l i' sp' t
      (VMeta i sp, t'           ) => solve l i sp t'
      (VU, VU) => pure ()
      -- REVIEW consider quoting back
      _ => error [DS "unify failed", DS (show t'), DS "=?=", DS (show u') ]

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi x Implicit a b => do
      m <- freshMeta ctx
      mv <- eval ctx.env CBN m
      insert ctx (App tm m) !(b $$ mv)
    va => pure (tm, va)

export
infer : Context -> Raw  -> M  (Tm, Val)

export
check : Context -> Raw -> Val  -> M  Tm
check ctx tm ty with (force ty)
  check ctx (RSrcPos x tm) _ | ty = check ({pos := x} ctx) tm ty
  check ctx t@(RLam nm icit tm) _ | ty = case ty of
          (VPi nm' icit' a b) => do
            putStrLn "icits \{nm} \{show icit} \{nm'} \{show icit'}"
            if icit == icit' then do
                let var = VVar (length ctx.env) [<]
                let ctx' = extend ctx nm a
                tm' <- check ctx' tm !(b $$ var)
                pure $ Lam nm icit tm'
              else if icit' == Implicit then do
                let var = VVar (length ctx.env) [<]
                ty' <- b $$ var
                sc <- check (extend ctx nm' a) t ty'
                pure $ Lam nm' icit' sc
              else
                error [(DS "Icity issue checking \{show t} at \{show ty}")]
          other => error [(DS "Expected pi type, got \{show !(quote 0 ty)}")]
  check ctx tm _ | (VPi nm' Implicit a b) = do
    putStrLn "XXX edge \{show tm} against VPi"
    let var = VVar (length ctx.env) [<]
    ty' <- b $$ var
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam nm' Implicit sc
  check ctx tm _ | ty = do
    -- We need to insert if it's not a Lam
    -- TODO figure out why the exception is here (cribbed from kovacs)
    (tm', ty') <- case !(infer ctx tm) of
      (tm'@(Lam{}),ty') => pure (tm', ty')
      (tm', ty') => insert ctx tm' ty'
    putStrLn "infer \{show tm} to \{show tm'} : \{show ty'} expect \{show ty}"
    when( ctx.lvl /= length ctx.env) $ error [DS "level mismatch \{show ctx.lvl} \{show ctx.env}"]
    unify ctx ctx.lvl ty' ty
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

  (icit, t, tty) <- case the Icit icit of
      Explicit => do
        (t, tty) <- infer ctx t
        (t, tty) <- insert ctx t tty
        pure (Explicit, t, tty)
      Implicit => do
        (t, tty) <- infer ctx t
        pure (Implicit, t, tty)

  (a,b) <- case !(forceMeta tty) of
    (VPi str icit' a b) => if icit' == icit then pure (a,b)
        else error [DS "IcitMismatch \{show icit} \{show icit'}"]

    -- If it's not a VPi, try to unify it with a VPi
    tty => do
      putStrLn "unify PI for \{show tty}"
      a <- eval ctx.env CBN !(freshMeta ctx)
      b <- MkClosure ctx.env <$> freshMeta (extend ctx "x" ?hole)
      unify ctx 0 tty (VPi "x" icit a b)
      pure (a,b)

  u <- check ctx u a
  pure (App t u, !(b $$ !(eval ctx.env CBN u)))

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

infer ctx (RLam nm icit tm) = do
  a <- freshMeta ctx >>= eval ctx.env CBN
  let ctx' = extend ctx nm a
  (tm', b) <- infer ctx' tm
  putStrLn "make lam for \{show nm} scope \{show tm'} : \{show b}"
  pure $ (Lam nm icit tm', VPi nm icit a $ MkClosure ctx.env !(quote (S ctx.lvl) b))
  -- error {ctx} [DS "can't infer lambda"]

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

module Lib.Check

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Control.Monad.Identity
import Lib.Parser.Impl
import Lib.Prettier
import Data.List
import Data.Vect
import Data.String
import Lib.Types
import Lib.TT
import Lib.TopContext
import Lib.Syntax

-- renaming
-- dom gamma ren
data Pden = PR Nat Nat (List Nat)

-- IORef for metas needs IO

forceMeta : Val -> M Val
forceMeta (VMeta ix sp) = case !(lookupMeta ix) of
  (Unsolved pos k xs) => pure (VMeta ix sp)
  (Solved k t) => vappSpine t sp
forceMeta x = pure x

-- Lennart needed more forcing for recursive nat,
forceType : Val -> M Val
forceType (VRef nm def sp) =
    case lookup nm !(get) of
      (Just (MkEntry name type (Fn t))) => vappSpine !(eval [] CBN t) sp
      _ => pure (VRef nm def sp)
forceType (VMeta ix sp) = case !(lookupMeta ix) of
  (Unsolved x k xs) => pure (VMeta ix sp)
  (Solved k t) => vappSpine t sp >>= forceType
forceType x = pure x


parameters (ctx: Context)
  -- return renaming, the position is the new VVar
  invert : Nat -> SnocList Val -> M (List Nat)
  invert lvl sp = go sp []
    where
      go : SnocList Val -> List Nat -> M (List Nat)
      go [<] acc = pure $ reverse acc
      go (xs :< VVar k [<]) acc = do
        if elem k acc
          then error [DS "non-linear pattern"]
          else go xs (k :: acc)
      go _ _ = error [DS "non-variable in pattern"]

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
        Nothing => error [DS "scope/skolem thinger"]
        Just x => goSpine ren lvl (Bnd $ cast x) sp
      go ren lvl (VRef nm def sp) = goSpine ren lvl (Ref nm def) sp
      go ren lvl (VMeta ix sp) = if ix == meta
        then error [DS "meta occurs check"]
        else goSpine ren lvl (Meta ix) sp
      go ren lvl (VLam n t) = pure (Lam n !(go (lvl :: ren) (S lvl) !(t $$ VVar lvl [<])))
      go ren lvl (VPi n icit ty tm) = pure (Pi n icit !(go ren lvl ty) !(go (lvl :: ren) (S lvl) !(tm $$ VVar lvl [<])))
      go ren lvl VU = pure U

  lams : Nat -> Tm -> Tm
  lams 0 tm = tm
  -- REVIEW can I get better names in here?
  lams (S k) tm = Lam "arg_\{show k}" (lams k tm)


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
  unifySpine l False _ _ = error [DS "unify failed at head"] -- unreachable now
  unifySpine l True [<] [<] = pure ()
  unifySpine l True (xs :< x) (ys :< y) = unify l x y >> unifySpine l True xs ys
  unifySpine l True _ _ = error [DS "meta spine length mismatch"]

  unify l t u = do
    debug "Unify \{show ctx.lvl}"
    debug "  \{show l} \{show t}"
    debug "  =?= \{show u}"
    t' <- forceMeta t
    u' <- forceMeta u
    case (t',u') of
      (VLam _ t,  VLam _ t') => unify (l + 1) !(t $$ VVar l [<]) !(t' $$ VVar l [<])
      (t,         VLam _ t') => unify (l + 1) !(t `vapp` VVar l [<]) !(t' $$ VVar l [<])
      (VLam _ t,  t'       ) => unify (l + 1) !(t $$ VVar l [<]) !(t' `vapp` VVar l [<])
      (VPi _ _ a b, VPi _ _ a' b') => unify l a a' >> unify (S l) !(b $$ VVar l [<]) !(b' $$ VVar l [<])
      (VVar k sp,   VVar k' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else error [DS "vvar mismatch \{show k} \{show k'}"]
      (VRef k def sp,   VRef k' def' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        -- REVIEW - consider forcing?
        else error [DS "vref mismatch \{show k} \{show k'}"]
      (VMeta k sp,  VMeta k' sp' ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else solve l k sp (VMeta k' sp')
      (t,           VMeta i' sp') => solve l i' sp' t
      (VMeta i sp, t'           ) => solve l i sp t'
      (VU, VU) => pure ()
      -- Lennart.newt cursed type references itself
      -- We _could_ look up the ref, eval against [] and vappSpine...
      (t,         VRef k' def sp') => do
        debug "expand \{show t} =?= %ref \{k'}"
        case lookup k' !(get) of
          Just (MkEntry name ty (Fn tm)) => unify l t !(vappSpine !(eval [] CBN tm) sp')
          _ => error [DS "unify failed \{show t'} =?= \{show u'} [no Fn]\n  env is \{show ctx.env} \{show $ map fst ctx.types}" ]
      -- REVIEW I'd like to quote this back, but we have l that aren't in the environment.
      _ => error [DS "unify failed \{show t'} =?= \{show u'} \n  env is \{show ctx.env} \{show $ map fst ctx.types}" ]

unifyCatch : Context -> Val -> Val -> M ()
unifyCatch ctx ty' ty = catchError (unify ctx ctx.lvl ty' ty) $ \(E x str) => do
    let names = toList $ map fst ctx.types
    a <- quote ctx.lvl ty'
    b <- quote ctx.lvl ty
    let msg = "\n  failed to unify \{pprint names a}\n    with \{pprint names b}\n  " <+> str
    throwError (E x msg)

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi x Implicit a b => do
      m <- freshMeta ctx
      mv <- eval ctx.env CBN m
      insert ctx (App tm m) !(b $$ mv)
    va => pure (tm, va)

lookupName : Context -> Raw -> M (Maybe (Tm, Val))
lookupName ctx (RVar nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M  (Maybe (Tm, Val))
    go i [] = case lookup nm !(get) of
      Just (MkEntry name ty def) => pure $ Just (Ref nm def, !(eval [] CBN ty))
      Nothing => pure Nothing
    go i ((x, ty) :: xs) = if x == nm then pure $ Just (Bnd i, ty)
      else go (i + 1) xs
lookupName ctx _ = pure Nothing


export
infer : Context -> Raw  -> M  (Tm, Val)

export
check : Context -> Raw -> Val  -> M  Tm

-- FIXME we need to switch to FC

checkAlt : Val -> Context -> Val -> RCaseAlt -> M CaseAlt
checkAlt scty ctx ty (MkAlt ptm body) = do
  -- we have a pattern term and a body
  (con, args) <- getArgs ptm []
  debug "ALT con \{con} args \{show args}"
  let Just (MkEntry _ dcty (DCon arity _)) = lookup con !(get)
    | _ => error [DS "expected datacon, got \{con}"]

  -- arity is wrong, but we actually need the type anyway
  -- in fact arity is for later (eval?) and we need to do implicits first
  debug "arity is \{show arity} dcty \{pprint [] dcty}"
  -- and then we run the names against the type
  -- get all that into a context and run the body

  -- So, how does this work?
  -- The constructor has arguments
  -- they may or may not be bound to names.
  -- their types may depend on nameless arguments
  -- the RHS is a function of some or all of this

  -- I suspect I'll rewrite this a few times
  vdcty <- eval [] CBN dcty
  debug "go \{show vdcty} \{show ptm}"
  alttm <- go vdcty ptm ctx
  debug "GOT \{pprint (names ctx) alttm}"

  -- package up the results into something.
  -- REVIEW args, also probably want the tag not the name.
  pure $ CaseCons con args alttm

  where

    go : Val -> Raw -> Context -> M Tm
    go ctype (RSrcPos x tm) ctx = go ctype tm ctx
    -- FIXME icit
    go (VPi str Explicit a b) (RApp t (RSrcPos _ (RVar nm)) Explicit) ctx = do
      debug "*** \{nm} : \{show a}"
      let var = VVar (length ctx.env) [<]
      let ctx' = extend ctx nm a
      Lam nm <$> go !(b $$ var) t ctx'
    go (VPi str Implicit a b) (RApp t (RSrcPos _ (RVar nm)) Implicit) ctx = do
      debug "*** \{nm} : \{show a}"
      let var = VVar (length ctx.env) [<]
      let ctx' = extend ctx nm a
      Lam nm <$> go !(b $$ var) t ctx'
    go (VPi str Implicit a b) t ctx = do
      let var = VVar (length ctx.env) [<]
      let ctx' = extend ctx "_" a
      Lam "_" <$> go !(b $$ var) t ctx'
    -- same deal with _ for name
    go (VPi str icit x y) (RApp t RImplicit icit') ctx = ?rhs_19
    go (VPi str icit x y) tm ctx = error {ctx} [DS "Can't use \{show tm} as pattern"]

    -- nameless variable
    go ctype RImplicit ctx = ?rhs_2
    go ctype (RVar nm) ctx = do
      debug "*** end"
      check ctx body ty
      -- pure ctx -- this should be our constructor.
    -- This happens if we run out of runway (more args and no pi)
    go ctype tm ctx = error {ctx} [DS "unhandled in go \{show ctype} \{show tm}"]

    getArgs : Raw -> List String -> M (String, List String)
    getArgs (RVar nm) acc = pure (nm, acc)
    -- TODO implicits
    getArgs (RApp t (RSrcPos _ (RVar nm)) icit) acc = getArgs t (nm :: acc)
    getArgs (RApp t (RVar nm) icit) acc = getArgs t (nm :: acc)
    getArgs (RApp t RHole icit) acc = getArgs t ("_" :: acc)
    getArgs (RSrcPos _ t) acc = getArgs t acc
    getArgs tm _ = error [DS "Patterns must be constructor and vars, got \{show tm}"]


check ctx tm ty = case (tm, !(forceType ty)) of
  (RCase rsc alts, ty) => do
    (sc, scty) <- infer ctx rsc
    let (VRef nm (TCon cnames) sp) = scty
      | _ => error [DS "expected TCon for scrutinee type, got: \{show scty}"]
    debug "constructor names \{show cnames}"
    alts' <- for alts $ checkAlt scty ctx ty
    pure $ Case sc alts'
    -- error [DS "implement check RCase sctype \{show scty}"]
  (RSrcPos x tm, ty) => check ({pos := x} ctx) tm ty
  -- Document a hole, pretend it's implemented
  (RHole, ty) => do
    ty' <- quote ctx.lvl ty
    let names = (toList $ map fst ctx.types)
    env <- for ctx.types $ \(n,ty) => pure "  \{n} : \{pprint names !(quote ctx.lvl ty)}"
    let msg = unlines (toList $ reverse env) ++ "  -----------\n" ++ "  goal \{pprint names ty'}"
    debug "INFO at \{show ctx.pos}: "
    debug msg
    -- let context = unlines foo
    -- need to print 'warning' with position
    -- fixme - just put a name on it like idris and stuff it into top.
    -- error [DS "hole:\n\{msg}"]
    pure $ Ref "?" Axiom  -- TODO - probably want hole opt on Def
  (t@(RLam nm icit tm), ty@(VPi nm' icit' a b)) => do
          debug "icits \{nm} \{show icit} \{nm'} \{show icit'}"
          if icit == icit' then do
              let var = VVar (length ctx.env) [<]
              let ctx' = extend ctx nm a
              tm' <- check ctx' tm !(b $$ var)
              pure $ Lam nm tm'
            else if icit' == Implicit then do
              let var = VVar (length ctx.env) [<]
              ty' <- b $$ var
              -- use nm' here if we want them automatically in scope
              sc <- check (extend ctx nm' a) t ty'
              pure $ Lam nm' sc
            else
              error [(DS "Icity issue checking \{show t} at \{show ty}")]
  (t@(RLam nm icit tm), ty) =>
            error [(DS "Expected pi type, got \{!(prvalCtx ty)}")]

  (tm, ty@(VPi nm' Implicit a b)) => do
    let names = toList $ map fst ctx.types
    debug "XXX edge add implicit lambda to \{show tm}"
    let var = VVar (length ctx.env) [<]
    ty' <- b $$ var
    debug "XXX ty' is \{!(prvalCtx {ctx=(extend ctx nm' a)} ty')}"
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam nm' sc

  (tm,ty) => do
    -- We need to insert if tm is not an Implicit Lam
    -- assuming all of the implicit ty have been handled above
    let names = toList $ map fst ctx.types
    (tm', ty') <- case !(infer ctx tm) of
      -- Kovacs doesn't insert on tm = Implicit Lam, we don't have Plicity there
      -- so I'll check the inferred type for an implicit pi
      (tm'@(Lam{}), ty'@(VPi _ Implicit _ _)) => do debug "Lambda"; pure (tm', ty')
      (tm', ty') => do
        debug "RUN INSERT ON \{pprint names tm'} at \{show ty'}"
        insert ctx tm' ty'

    debug "INFER \{show tm} to (\{pprint names tm'} : \{show ty'}) expect \{show ty}"
    unifyCatch ctx ty' ty
    pure tm'

infer ctx (RVar nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M  (Tm, Val)
    go i [] = case lookup nm !(get) of
      Just (MkEntry name ty def) => do
        debug "lookup \{name} as \{show def}"
        pure (Ref nm def, !(eval [] CBN ty))
      Nothing => error [DS "\{show nm} not in scope"]
    go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd i, ty)
      else go (i + 1) xs
  -- need environment of name -> type..
infer ctx (RApp t u icit) = do
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
    -- TODO test case to cover this.
    tty => do
      debug "unify PI for \{show tty}"
      a <- eval ctx.env CBN !(freshMeta ctx)
      b <- MkClosure ctx.env <$> freshMeta (extend ctx ":ins" a)
      unify ctx 0 tty (VPi ":ins" icit a b)
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
  debug "make lam for \{show nm} scope \{pprint (names ctx) tm'} : \{show b}"
  pure $ (Lam nm tm', VPi nm icit a $ MkClosure ctx.env !(quote (S ctx.lvl) b))
  -- error {ctx} [DS "can't infer lambda"]

infer ctx RImplicit = do
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

-- The idea here is to insert a hole for a parse error
-- but the parser doesn't emit this yet.
-- infer ctx (RParseError str) = ?todo_insert_meta

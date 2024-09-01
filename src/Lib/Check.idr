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
forceMeta (VMeta fc ix sp) = case !(lookupMeta ix) of
  (Unsolved pos k xs) => pure (VMeta fc ix sp)
  (Solved k t) => vappSpine t sp
forceMeta x = pure x

-- Lennart needed more forcing for recursive nat,
forceType : Val -> M Val
forceType (VRef fc nm def sp) =
    case lookup nm !(get) of
      (Just (MkEntry name type (Fn t))) => vappSpine !(eval [] CBN t) sp
      _ => pure (VRef fc nm def sp)
forceType (VMeta fc ix sp) = case !(lookupMeta ix) of
  (Unsolved x k xs) => pure (VMeta fc ix sp)
  (Solved k t) => vappSpine t sp >>= forceType
forceType x = pure x


parameters (ctx: Context)
  -- return renaming, the position is the new VVar
  invert : Nat -> SnocList Val -> M (List Nat)
  invert lvl sp = go sp []
    where
      go : SnocList Val -> List Nat -> M (List Nat)
      go [<] acc = pure $ reverse acc
      go (xs :< VVar emptyFC k [<]) acc = do
        if elem k acc
          then error emptyFC "non-linear pattern"
          else go xs (k :: acc)
      go _ _ = error emptyFC "non-variable in pattern"

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
        goSpine ren lvl (App emptyFC tm xtm) xs

      go ren lvl (VVar fc k sp) = case findIndex (== k) ren of
        Nothing => error emptyFC "scope/skolem thinger"
        Just x => goSpine ren lvl (Bnd fc $ cast x) sp
      go ren lvl (VRef fc nm def sp) = goSpine ren lvl (Ref fc nm def) sp
      go ren lvl (VMeta fc ix sp) = if ix == meta
        -- REVIEW is this the right fc?
        then error fc "meta occurs check"
        else goSpine ren lvl (Meta fc ix) sp
      go ren lvl (VLam fc n t) = pure (Lam fc n !(go (lvl :: ren) (S lvl) !(t $$ VVar emptyFC lvl [<])))
      go ren lvl (VPi fc n icit ty tm) = pure (Pi fc n icit !(go ren lvl ty) !(go (lvl :: ren) (S lvl) !(tm $$ VVar emptyFC lvl [<])))
      go ren lvl (VU fc) = pure (U fc)
      go ren lvl (VCase fc sc alts) = error fc "Case in solution"
          -- This seems dicey, for VLam we eval and then process the levels.
          -- Here we have raw Tm so we haven't even done occurs check. I'm thinking
          -- we don't allow solutions with Case in them
          -- pure (Case fc !(go ren lvl sc) alts)
      go ren lvl (VLit fc lit) = pure (Lit fc lit)

  lams : Nat -> Tm -> Tm
  lams 0 tm = tm
  -- REVIEW can I get better names in here?
  lams (S k) tm = Lam emptyFC "arg_\{show k}" (lams k tm)


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
  unifySpine l False _ _ = error emptyFC "unify failed at head" -- unreachable now
  unifySpine l True [<] [<] = pure ()
  unifySpine l True (xs :< x) (ys :< y) = unify l x y >> unifySpine l True xs ys
  unifySpine l True _ _ = error emptyFC "meta spine length mismatch"

  unify l t u = do
    debug "Unify \{show ctx.lvl}"
    debug "  \{show l} \{show t}"
    debug "  =?= \{show u}"
    t' <- forceMeta t
    u' <- forceMeta u
    debug "forced \{show t'}"
    debug "  =?= \{show u'}"
    debug "env \{show ctx.env}"
    case (t',u') of
      (VLam _ _ t,  VLam _ _ t') => unify (l + 1) !(t $$ VVar emptyFC l [<]) !(t' $$ VVar emptyFC l [<])
      (t,         VLam fc' _ t') => unify (l + 1) !(t `vapp` VVar emptyFC l [<]) !(t' $$ VVar emptyFC l [<])
      (VLam fc _ t,  t'       ) => unify (l + 1) !(t $$ VVar emptyFC l [<]) !(t' `vapp` VVar emptyFC l [<])
      (VPi fc _ _ a b, VPi fc' _ _ a' b') => unify l a a' >> unify (S l) !(b $$ VVar emptyFC l [<]) !(b' $$ VVar emptyFC l [<])
      (VVar fc k sp,   VVar fc' k' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else error emptyFC "vvar mismatch \{show k} \{show k'}"
      (VRef fc k def sp,   VRef fc' k' def' sp'  ) =>
        if k == k' then do
          debug "unify \{show l} spine at \{k} \{show sp} \{show sp'}"
          unifySpine l (k == k') sp sp'
        -- REVIEW - consider forcing?
        else error emptyFC "vref mismatch \{show k} \{show k'} -- \{show sp} \{show sp'}"
      (VMeta fc k sp,  VMeta fc' k' sp' ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else solve l k sp (VMeta fc' k' sp')
      (t,           VMeta fc' i' sp') => solve l i' sp' t
      (VMeta fc i sp, t'           ) => solve l i sp t'
      (VU _, VU _) => pure ()
      -- Lennart.newt cursed type references itself
      -- We _could_ look up the ref, eval against [] and vappSpine...
      (t,         VRef fc' k' def sp') => do
        debug "expand \{show t} =?= %ref \{k'}"
        case lookup k' !(get) of
          Just (MkEntry name ty (Fn tm)) => unify l t !(vappSpine !(eval [] CBN tm) sp')
          _ => error ctx.fc "unify failed \{show t'} =?= \{show u'} [no Fn]\n  env is \{show ctx.env} \{show $ map fst ctx.types}"
      -- REVIEW I'd like to quote this back, but we have l that aren't in the environment.
      _ => error ctx.fc "unify failed \{show t'} =?= \{show u'} \n  env is \{show ctx.env} \{show $ map fst ctx.types}"

unifyCatch : FC -> Context -> Val -> Val -> M ()
unifyCatch fc ctx ty' ty = catchError (unify ctx ctx.lvl ty' ty) $ \(E x str) => do
    let names = toList $ map fst ctx.types
    debug "fail \{show ty'} \{show ty}"
    a <- quote ctx.lvl ty'
    b <- quote ctx.lvl ty
    let msg = "\n  failed to unify \{pprint names a}\n    with \{pprint names b}\n  " <+> str
    throwError (E fc msg)

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi fc x Implicit a b => do
      m <- freshMeta ctx fc
      mv <- eval ctx.env CBN m
      insert ctx (App emptyFC tm m) !(b $$ mv)
    va => pure (tm, va)

lookupName : Context -> Raw -> M (Maybe (Tm, Val))
lookupName ctx (RVar fc nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M  (Maybe (Tm, Val))
    go i [] = case lookup nm !(get) of
      Just (MkEntry name ty def) => pure $ Just (Ref fc nm def, !(eval [] CBN ty))
      Nothing => pure Nothing
    go i ((x, ty) :: xs) = if x == nm then pure $ Just (Bnd fc i, ty)
      else go (i + 1) xs
lookupName ctx _ = pure Nothing


primType : FC -> String -> M Val
primType fc nm = case lookup nm !(get) of
      Just (MkEntry name ty PrimTCon) => pure $ VRef fc name PrimTCon [<]
      _ => error fc "Primitive type \{show nm} not in scope"


export
infer : Context -> Raw  -> M  (Tm, Val)

export
check : Context -> Raw -> Val  -> M  Tm


-- This is the old case checking that expected a user-supplied case tree
checkAlt : Val -> Context -> Val -> RCaseAlt -> M CaseAlt
checkAlt scty ctx ty (MkAlt ptm body) = do
  -- we have a pattern term and a body
  (con, args) <- getArgs ptm []
  debug "ALT con \{con} args \{show args}"
  let Just (MkEntry _ dcty (DCon arity _)) = lookup con !(get)
    | Nothing => do
        -- check body with con bound at scty against ty
        let ctx' = extend ctx con scty
        body' <- check ctx' body ty
        pure $ CaseDefault body'
    | _ => error emptyFC "expected datacon, got \{con}"

  -- arity is wrong, but we actually need the type anyway
  -- in fact arity is for later (eval?) and we need to do implicits first
  debug "arity is \{show arity} dcty \{pprint [] dcty} con \{show con} pats \{show args}"
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
  alttm <- go vdcty args ctx
  debug "GOT \{pprint (names ctx) alttm}"

  -- package up the results into something.
  -- REVIEW args, also probably want the tag not the name.
  pure $ CaseCons con (map (snd . snd) args) alttm

  where
    argsFC : List (FC, Icit, String) -> FC
    argsFC [] = emptyFC
    argsFC ((fc,_) :: xs) = fc

    go : Val -> List (FC, Icit, String) -> Context -> M Tm
    -- FIXME icit
    -- backwards?
    go (VPi fc str Explicit a b) ((fc', Explicit, nm) :: rest) ctx = do
      debug "*** \{nm} : \{show a} Explicit \{str}"
      let var = VVar fc' (length ctx.env) [<]
      let ctx' = extend ctx nm a
      Lam fc' nm <$> go !(b $$ var) rest ctx'
    go (VPi fc str Implicit a b) ((fc', Implicit, nm) :: rest) ctx = do
      debug "*** \{nm} : \{show a} Implicit \{str}"
      let var = VVar emptyFC (length ctx.env) [<]
      let ctx' = extend ctx nm a
      Lam emptyFC nm <$> go !(b $$ var) rest ctx'

    go (VPi _ str Implicit a b) args ctx = do
      debug "*** insert \{str}"
      let fc' = argsFC args
      let var = VVar fc' (length ctx.env) [<]
      let ctx' = extend ctx "_" a
      Lam fc' "_" <$> go !(b $$ var) args ctx'
    -- same deal with _ for name
    go (VPi fc str Explicit a b) ((fc', Implicit, nm) :: rest) ctx = do
      error fc' "Implicit/Explicit mismatch \{show str} at \{show nm}"
    go (VPi fc str icit x y) [] ctx = error emptyFC "Not enough arguments"

    -- nameless variable
    go ctype [] ctx = do
      debug "*** end \{show ctype}"
      -- FIXME FIXME - I think I should be unifying ctype against scty and learning stuff from it
      -- like n = S k.
      -- debug "Unifying constructor"
      -- unifyCatch emptyFC ctx ctype scty
      -- my first example has issues with Vect Z 0 =?=

      check ctx body ty
    -- This happens if we run out of runway (more args and no pi)
    -- go ctype tm ctx = error (getF "unhandled in checkAlt.go type: \{show ctype} term: \{show tm}"
    go ctype args ctx = error (argsFC args) "Extra args"
    getArgs : Raw -> List (FC,Icit, String) -> M (String, List (FC,Icit, String))
    getArgs (RVar _ nm) acc = pure (nm, acc)
    -- TODO implicits
    getArgs (RApp _ t (RVar fc nm) icit) acc = getArgs t ((fc,icit,nm) :: acc)
    getArgs (RApp _ t (RHole fc) icit) acc = getArgs t ((fc,icit,"_") :: acc)
    getArgs tm _ = error (getFC tm) "Patterns must be constructor and vars, got \{show tm}"


check ctx tm ty = case (tm, !(forceType ty)) of
  -- previous code
  -- (RCase fc rsc alts, ty) => do
  --   (sc, scty) <- infer ctx rsc
  --   let (VRef fc nm (TCon cnames) sp) = scty
  --     | _ => error fc "expected TCon for scrutinee type, got: \{show scty}"
  --   debug "constructor names \{show cnames}"
  --   alts' <- for alts $ checkAlt scty ctx ty
  --   pure $ Case emptyFC sc alts'
  (RCase fc rsc alts, ty) => do
    -- scrutinee must infer.  We will probably want to `let` it too.
    (sc, scty) <- infer ctx rsc
    let (VRef fc nm (TCon cnames) sp) = scty
      | _ => error fc "expected TCon for scrutinee type, got: \{show scty}"
    debug "constructor names \{show cnames}"
    alts' <- for alts $ checkAlt scty ctx ty
    pure $ Case emptyFC sc alts'
  -- Document a hole, pretend it's implemented
  (RHole fc, ty) => do
    ty' <- quote ctx.lvl ty
    let names = (toList $ map fst ctx.types)
    env <- for ctx.types $ \(n,ty) => pure "  \{n} : \{pprint names !(quote ctx.lvl ty)}"
    let msg = unlines (toList $ reverse env) ++ "  -----------\n" ++ "  goal \{pprint names ty'}"
    liftIO $ putStrLn "INFO at \{show fc}: "
    liftIO $ putStrLn msg
    -- let context = unlines foo
    -- need to print 'warning' with position
    -- fixme - just put a name on it like idris and stuff it into top.
    -- error [DS "hole:\n\{msg}"]
    pure $ Ref emptyFC "?" Axiom  -- TODO - probably want hole opt on Def
  (t@(RLam fc nm icit tm), ty@(VPi fc' nm' icit' a b)) => do
          debug "icits \{nm} \{show icit} \{nm'} \{show icit'}"
          if icit == icit' then do
              let var = VVar fc (length ctx.env) [<]
              let ctx' = extend ctx nm a
              tm' <- check ctx' tm !(b $$ var)
              pure $ Lam emptyFC nm tm'
            else if icit' == Implicit then do
              let var = VVar fc (length ctx.env) [<]
              ty' <- b $$ var
              -- use nm' here if we want them automatically in scope
              sc <- check (extend ctx nm' a) t ty'
              pure $ Lam fc nm' sc
            else
              error fc "Icity issue checking \{show t} at \{show ty}"
  (t@(RLam fc nm icit tm), ty) =>
            error fc "Expected pi type, got \{!(prvalCtx ty)}"

  (tm, ty@(VPi fc nm' Implicit a b)) => do
    let names = toList $ map fst ctx.types
    debug "XXX edge add implicit lambda to \{show tm}"
    let var = VVar fc (length ctx.env) [<]
    ty' <- b $$ var
    debug "XXX ty' is \{!(prvalCtx {ctx=(extend ctx nm' a)} ty')}"
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam (getFC tm) nm' sc

  (tm,ty) => do
    -- We need to insert if tm is not an Implicit Lam
    -- assuming all of the implicit ty have been handled above
    let names = toList $ map fst ctx.types
    (tm', ty') <- case !(infer ctx tm) of
      -- Kovacs doesn't insert on tm = Implicit Lam, we don't have Plicity there
      -- so I'll check the inferred type for an implicit pi
      (tm'@(Lam{}), ty'@(VPi _ _ Implicit _ _)) => do debug "Lambda"; pure (tm', ty')
      (tm', ty') => do
        debug "RUN INSERT ON \{pprint names tm'} at \{show ty'}"
        insert ctx tm' ty'

    debug "INFER \{show tm} to (\{pprint names tm'} : \{show ty'}) expect \{show ty}"
    unifyCatch (getFC tm) ctx ty' ty
    pure tm'

infer ctx (RVar fc nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M  (Tm, Val)
    go i [] = case lookup nm !(get) of
      Just (MkEntry name ty def) => do
        debug "lookup \{name} as \{show def}"
        pure (Ref fc nm def, !(eval [] CBN ty))
      Nothing => error fc "\{show nm} not in scope"
    go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd fc i, ty)
      else go (i + 1) xs
  -- need environment of name -> type..
infer ctx (RApp fc t u icit) = do
  (icit, t, tty) <- case the Icit icit of
      Explicit => do
        (t, tty) <- infer ctx t
        (t, tty) <- insert ctx t tty
        pure (Explicit, t, tty)
      Implicit => do
        (t, tty) <- infer ctx t
        pure (Implicit, t, tty)

  (a,b) <- case !(forceMeta tty) of
    (VPi fc str icit' a b) => if icit' == icit then pure (a,b)
        else error fc "IcitMismatch \{show icit} \{show icit'}"

    -- If it's not a VPi, try to unify it with a VPi
    -- TODO test case to cover this.
    tty => do
      debug "unify PI for \{show tty}"
      a <- eval ctx.env CBN !(freshMeta ctx fc)
      b <- MkClosure ctx.env <$> freshMeta (extend ctx ":ins" a) fc
      unify ctx 0 tty (VPi fc ":ins" icit a b)
      pure (a,b)

  u <- check ctx u a
  pure (App fc t u, !(b $$ !(eval ctx.env CBN u)))

infer ctx (RU fc) = pure (U fc, VU fc) -- YOLO
infer ctx (RPi fc nm icit ty ty2) = do
  ty' <- check ctx ty (VU fc)
  vty' <- eval ctx.env CBN ty'
  let nm := fromMaybe "_" nm
  ty2' <- check (extend ctx nm vty') ty2 (VU fc)
  pure (Pi fc nm icit ty' ty2', (VU fc))
infer ctx (RLet fc str tm tm1 tm2) = error fc "implement RLet"
infer ctx (RAnn fc tm rty) = do
  ty <- check ctx rty (VU fc)
  vty <- eval ctx.env CBN ty
  tm <- check ctx tm vty
  pure (tm, vty)

infer ctx (RLam fc nm icit tm) = do
  a <- freshMeta ctx fc >>= eval ctx.env CBN
  let ctx' = extend ctx nm a
  (tm', b) <- infer ctx' tm
  debug "make lam for \{show nm} scope \{pprint (names ctx) tm'} : \{show b}"
  pure $ (Lam fc nm tm', VPi fc nm icit a $ MkClosure ctx.env !(quote (S ctx.lvl) b))
  -- error {ctx} [DS "can't infer lambda"]

infer ctx (RImplicit fc) = do
  ty <- freshMeta ctx fc
  vty <- eval ctx.env CBN ty
  tm <- freshMeta ctx fc
  pure (tm, vty)

infer ctx (RLit fc (LString str)) = pure (Lit fc (LString str), !(primType fc "String"))
infer ctx (RLit fc (LInt i)) = pure (Lit fc (LInt i), !(primType fc "Int"))

infer ctx tm = error (getFC tm) "Implement infer \{show tm}"

-- The idea here is to insert a hole for a parse error
-- but the parser doesn't emit this yet.
-- infer ctx (RParseError str) = ?todo_insert_meta

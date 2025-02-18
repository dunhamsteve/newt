module Lib.Elab

import Lib.Parser.Impl
import Lib.Prettier
import Data.List
import Data.Vect
import Data.String
import Data.IORef
import Lib.Types
import Lib.Util
import Lib.Eval
import Lib.TopContext
import Lib.Syntax




||| collectDecl collects multiple Def for one function into one
export
collectDecl : List Decl -> List Decl
collectDecl [] = []
collectDecl ((Def fc nm cl) :: rest@(Def _ nm' cl' :: xs)) =
  if nm == nm' then collectDecl (Def fc nm (cl ++ cl') :: xs)
  else (Def fc nm cl :: collectDecl rest)
collectDecl (x :: xs) = x :: collectDecl xs

-- renaming
-- dom gamma ren
data Pden = PR Nat Nat (List Nat)

showCtx : Context -> M String
showCtx ctx =
  unlines . reverse <$> go (names ctx) 0 (reverse $ zip ctx.env (toList ctx.types)) []
  where
    isVar : Nat -> Val -> Bool
    isVar k (VVar _ k' [<]) = k == k'
    isVar _ _ = False

    go : List String -> Nat -> List (Val, String, Val) -> List String -> M (List String)
    go _ _ [] acc = pure acc
    go names k ((v, n, ty) :: xs) acc = if isVar k v
      -- TODO - use Doc and add <+/> as appropriate to printing
      then go names (S k) xs ("  \{n} : \{pprint names !(quote ctx.lvl ty)}":: acc)
      else go names (S k) xs ("  \{n} = \{pprint names !(quote ctx.lvl v)} : \{pprint names !(quote ctx.lvl ty)}":: acc)

dumpCtx : Context -> M String
dumpCtx ctx = do
  let names = (toList $ map fst ctx.types)
  -- I want to know which ones are defines. I should skip the `=` bit if they match, I'll need indices in here too.
  env <- for (zip ctx.env (toList ctx.types)) $ \(v, n, ty) => pure "  \{n} : \{pprint names !(quote ctx.lvl ty)} = \{pprint names !(quote ctx.lvl v)}"
  let msg = unlines (toList $ reverse env) -- ++ "  -----------\n" ++ "  goal \{pprint names ty'}"
  pure msg


pprint : Context -> Val -> M Doc
pprint ctx v = pure $ pprint (names ctx) !(quote (length ctx.env) v)

||| return Bnd and type for name
export
lookupName : Context -> String  -> Maybe (Tm, Val)
lookupName ctx name = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val) -> Maybe (Tm, Val)
    go ix [] = Nothing
    -- FIXME - we should stuff a Binder of some sort into "types"
    go ix ((nm, ty) :: xs) = if nm == name then Just (Bnd emptyFC ix, ty) else go (S ix) xs

export
lookupDef : Context -> String  -> Maybe Val
lookupDef ctx name = go 0 ctx.types ctx.env
  where
    go : Nat -> Vect n (String, Val) -> List Val -> Maybe Val
    go ix ((nm, ty) :: xs) (v :: vs) = if nm == name then Just v else go (S ix) xs vs
    go ix _ _ = Nothing


-- IORef for metas needs IO
export
forceMeta : Val -> M Val
forceMeta (VMeta fc ix sp) = case !(lookupMeta ix) of
  (Unsolved pos k xs _ _ _) => pure (VMeta fc ix sp)
  (Solved _ k t) => vappSpine t sp >>= forceMeta
forceMeta x = pure x

public export
record UnifyResult where
  constructor MkResult
  -- wild guess here - lhs is a VVar
  constraints : List (Nat, Val)

Semigroup UnifyResult where
  (MkResult cs) <+> (MkResult cs') = MkResult (cs ++ cs')

Monoid UnifyResult where
  neutral = MkResult []

data UnifyMode = Normal | Pattern


export
check : Context -> Raw -> Val -> M Tm

export
unifyCatch : FC -> Context -> Val -> Val -> M ()

-- Check that the arguments are not explicit and the type constructor in codomain matches
-- Later we will build a table of codomain type, and maybe make the user tag the candidates
-- like Idris does with %hint
isCandidate : Val -> Tm -> Bool
isCandidate ty (Pi fc nm Explicit rig t u) = False
isCandidate ty (Pi fc nm icit rig t u) = isCandidate ty u
isCandidate (VRef _ nm _ _) (Ref fc nm' def) = nm == nm'
isCandidate ty (App fc t u) = isCandidate ty t
isCandidate _ _ = False

-- This is a crude first pass
export
findMatches : Context -> Val -> List TopEntry -> M (List String)
findMatches ctx ty [] = pure []
findMatches ctx ty ((MkEntry _ name type def) :: xs) = do
  let True = isCandidate ty type | False => findMatches ctx ty xs
  top <- get
  -- let ctx = mkCtx (getFC ty)
  -- FIXME we're restoring state, but the INFO logs have already been emitted
  -- Also redo this whole thing to run during elab, recheck constraints, etc.
  mc <- readIORef top.metaCtx
  catchError(do
      -- TODO sort out the FC here
      let fc = getFC ty
      debug "TRY \{name} : \{pprint [] type} for \{show ty}"
      -- This check is solving metas, so we save mc below in case we want this solution
      -- tm <- check (mkCtx fc) (RVar fc name) ty
      -- FIXME RVar should optionally have qualified names
      let (QN ns nm) = name
      let (cod, tele) = splitTele type
      modifyIORef top.metaCtx { mcmode := CheckFirst }
      tm <- check ctx (RVar fc nm) ty
      debug "Found \{pprint [] tm} for \{show ty}"
      writeIORef top.metaCtx mc
      (nm ::) <$> findMatches ctx ty xs)
    (\ err => do
      debug "No match \{show ty} \{pprint [] type} \{showError "" err}"
      writeIORef top.metaCtx mc
      findMatches ctx ty xs)

export
contextMatches : Context -> Val -> M (List (Tm, Val))
contextMatches ctx ty = go (zip ctx.env (toList ctx.types))
  where
    go : List (Val, String, Val) -> M (List (Tm, Val))
    go [] = pure []
    go ((tm, nm, vty) :: xs) = do
      type <- quote ctx.lvl vty
      let True = isCandidate ty type | False => go xs
      top <- get
      mc <- readIORef top.metaCtx
      catchError(do
          debug "TRY context \{nm} : \{pprint (names ctx) type} for \{show ty}"
          unifyCatch (getFC ty) ctx ty vty
          mc' <- readIORef top.metaCtx
          writeIORef top.metaCtx mc
          tm <- quote ctx.lvl tm
          ((tm, vty) ::) <$> go xs)
        (\ err => do
          debug "No match \{show ty} \{pprint (names ctx) type} \{showError "" err}"
          writeIORef top.metaCtx mc
          go xs)

export
getArity : Tm -> Nat
getArity (Pi x str icit rig t u) = S (getArity u)
-- Ref or App (of type constructor) are valid
getArity _ = Z

-- Can metas live in context for now?
-- We'll have to be able to add them, which might put gamma in a ref



-- Makes the arg for `solve` when we solve an auto
makeSpine : Nat -> Vect k BD -> SnocList Val
makeSpine k [] = [<]
makeSpine (S k) (Defined :: xs) = makeSpine k xs
makeSpine (S k) (Bound :: xs) = makeSpine k xs :< VVar emptyFC k [<]
makeSpine 0 xs = ?fixme

export
solve : Env -> (k : Nat) -> SnocList Val -> Val -> M ()


export
trySolveAuto : MetaEntry -> M Bool
trySolveAuto (Unsolved fc k ctx ty AutoSolve _) = do
      debug "TRYAUTO solving \{show k} : \{show ty}"
      -- fill in solved metas in type
      x <- quote ctx.lvl ty
      ty <- eval ctx.env CBN x
      debug "AUTO ---> \{show ty}"
      -- we want the context here too.
      top <- get
      [] <- contextMatches ctx ty
          | [(tm, vty)] => do
              unifyCatch (getFC ty) ctx ty vty
              val <- eval ctx.env CBN tm
              debug "SOLUTION \{pprint [] tm} evaled to \{show val}"
              let sp = makeSpine ctx.lvl ctx.bds
              solve ctx.env k sp val
              pure True
          | res => do
              debug "FAILED to solve \{show ty}, matches: \{commaSep $ map (pprint [] . fst) res}"
              pure False
      [nm] <- findMatches ctx ty $ toList top.defs
        | res => do
          debug "FAILED to solve \{show ty}, matches: \{show res}"
          pure False
      tm <- check ctx (RVar fc nm) ty
      val <- eval ctx.env CBN tm
      debug "SOLUTION \{pprint [] tm} evaled to \{show val}"
      let sp = makeSpine ctx.lvl ctx.bds
      solve ctx.env k sp val
      pure True
trySolveAuto _ = pure False

-- export
-- solveAutos : Nat -> List MetaEntry -> M ()
-- solveAutos mstart [] = pure ()
-- solveAutos mstart (entry :: es) = do
--       res <- trySolveAuto entry
--       -- idris is inlining this and blowing stack?
--       if res
--         then do
--           top <- get
--           mc <- readIORef top.metaCtx
--           let mlen = length mc.metas `minus` mstart
--           solveAutos mstart (take mlen mc.metas)
--         else
--           solveAutos mstart es


-- Called from ProcessDecl, this was popping the stack, the tail call optimization doesn't
-- handle the traversal of the entire meta list.  I've turned the restart into a trampoline
-- and filtered it down to unsolved autos.
export
solveAutos : Nat -> M ()
solveAutos mstart = do
  top <- get
  mc <- readIORef top.metaCtx
  let mlen = length mc.metas `minus` mstart
  res <- run $ filter isAuto (take mlen mc.metas)
  if res then solveAutos mstart else pure ()
  where
    isAuto : MetaEntry -> Bool
    isAuto (Unsolved fc k ctx x AutoSolve xs) = True
    isAuto _ = False

    run : List MetaEntry -> M Bool
    run Nil = pure False
    run (e :: es) =
      if !(trySolveAuto e) then pure True else run es

-- We need to switch to SortedMap here
export
updateMeta : Nat -> (MetaEntry -> M MetaEntry) -> M ()
updateMeta ix f = do
  top <- get
  mc <- readIORef top.metaCtx
  metas <- go mc.metas
  writeIORef top.metaCtx $ {metas := metas} mc
  where
    go : List MetaEntry -> M (List MetaEntry)
    go [] = error' "Meta \{show ix} not found"
    go (x@((Unsolved y k z w v ys)) :: xs) = if k == ix then (::xs) <$> f x else (x ::) <$> go xs
    go (x@((Solved _ k y)) :: xs) = if k == ix then (::xs) <$> f x else (x ::) <$> go xs


checkAutos : Nat -> List MetaEntry -> M ()
checkAutos ix Nil = pure ()
checkAutos ix (entry@(Unsolved fc k ctx ty AutoSolve _) :: rest) = do
  ty' <- quote ctx.lvl ty
  when (usesMeta ty') $ ignore $ trySolveAuto entry
  checkAutos ix rest
  where
    usesMeta : Tm -> Bool
    usesMeta (App _ (Meta _ k) u) = if k == ix then True else usesMeta u
    usesMeta (App _ _ u) = usesMeta u
    usesMeta _ = False
checkAutos ix (_ :: rest) = checkAutos ix rest


export
addConstraint : Env -> Nat -> SnocList Val -> Val -> M ()
addConstraint env ix sp tm = do
  top <- get
  mc <- readIORef top.metaCtx
  let (CheckAll) = mc.mcmode | _ => pure ()
  updateMeta ix $ \case
    (Unsolved pos k a b c cons) => do
      debug "Add constraint m\{show ix} \{show sp} =?= \{show tm}"
      pure (Unsolved pos k a b c (MkMc (getFC tm) env sp tm :: cons))
    (Solved _ k tm) => error' "Meta \{show k} already solved [addConstraint]"
  mc <- readIORef top.metaCtx
  checkAutos ix mc.metas
  -- this loops too
  -- solveAutos 0 mc.metas
  pure ()


-- return renaming, the position is the new VVar
invert : Nat -> SnocList Val -> M (List Nat)
invert lvl sp = go sp []
  where
    go : SnocList Val -> List Nat -> M (List Nat)
    go [<] acc = pure $ reverse acc
    go (xs :< VVar fc k [<]) acc = do
      if elem k acc
        then do
          debug "\{show k} \{show acc}"
          -- when does this happen?
          error fc "non-linear pattern: \{show sp}"
        else go xs (k :: acc)
    go (xs :< v) _ = error emptyFC "non-variable in pattern \{show v}"


-- REVIEW why am I converting to Tm?
-- we have to "lift" the renaming when we go under a lambda
-- I think that essentially means our domain ix are one bigger, since we're looking at lvl
-- in the codomain, so maybe we can just keep that value


rename : Nat -> List Nat -> Nat -> Val  -> M Tm

renameSpine : Nat -> List Nat -> Nat -> Tm -> SnocList Val  -> M Tm
renameSpine meta ren lvl tm [<] = pure tm
renameSpine meta ren lvl tm (xs :< x) = do
  xtm <- rename meta ren lvl x
  pure $ App emptyFC !(renameSpine meta ren lvl tm xs) xtm




rename meta ren lvl (VVar fc k sp) = case findIndex (== k) ren of
  Nothing => error fc "scope/skolem thinger VVar \{show k} ren \{show ren}"
  Just x => renameSpine meta ren lvl (Bnd fc $ cast x) sp
rename meta ren lvl (VRef fc nm def sp) = renameSpine meta ren lvl (Ref fc nm def) sp
rename meta ren lvl (VMeta fc ix sp) = do
  -- So sometimes we have an unsolved meta in here which reference vars out of scope.
  debug "rename Meta \{show ix} spine \{show sp}"
  if ix == meta
  -- REVIEW is this the right fc?
    then error fc "meta occurs check"
    else case !(lookupMeta ix) of
      Solved fc _ val => do
        debug "rename: \{show ix} is solved"
        rename meta ren lvl !(vappSpine val sp)
      _ => do
        debug "rename: \{show ix} is unsolved"
        catchError (renameSpine meta ren lvl (Meta fc ix) sp) (\err => throwError $ Postpone fc ix (errorMsg err))
rename meta ren lvl (VLam fc n icit rig t) = pure (Lam fc n icit rig !(rename meta (lvl :: ren) (S lvl) !(t $$ VVar fc lvl [<])))
rename meta ren lvl (VPi fc n icit rig ty tm) = pure (Pi fc n icit rig !(rename meta ren lvl ty) !(rename meta (lvl :: ren) (S lvl) !(tm $$ VVar emptyFC lvl [<])))
rename meta ren lvl (VU fc) = pure (UU fc)
rename meta ren lvl (VErased fc) = pure (Erased fc)
-- for now, we don't do solutions with case in them.
rename meta ren lvl (VCase fc sc alts) = error fc "Case in solution"
rename meta ren lvl (VLit fc lit) = pure (Lit fc lit)
rename meta ren lvl (VLet fc name val body) =
  pure $ Let fc name !(rename meta ren lvl val) !(rename meta (lvl :: ren) (S lvl) body)
-- these probably shouldn't show up in solutions...
rename meta ren lvl (VLetRec fc name ty val body) =
  pure $ LetRec fc name !(rename meta ren lvl ty) !(rename meta (lvl :: ren) (S lvl) val) !(rename meta (lvl :: ren) (S lvl) body)

lams : Nat -> List String -> Tm -> Tm
lams 0 _ tm = tm
-- REVIEW do we want a better FC, icity?, rig?
lams (S k) [] tm = Lam emptyFC "arg_\{show k}" Explicit Many (lams k [] tm)
lams (S k) (x :: xs) tm = Lam emptyFC x Explicit Many (lams k xs tm)

export
unify : Env -> UnifyMode -> Val -> Val  -> M UnifyResult

(.boundNames) : Context -> List String
ctx.boundNames = map snd $ filter (\x => fst x == Bound) $ toList $ zip ctx.bds (map fst ctx.types)


maybeCheck : M () -> M ()
maybeCheck action = do
  top <- get
  mc <- readIORef top.metaCtx
  case mc.mcmode of
    CheckAll => action
    CheckFirst => do
      modifyIORef top.metaCtx $ { mcmode := NoCheck }
      action
      modifyIORef top.metaCtx $ { mcmode := CheckFirst }
    NoCheck => pure ()

solve env m sp t = do
  meta@(Unsolved metaFC ix ctx_ ty kind cons) <- lookupMeta m
    | _ => error (getFC t) "Meta \{show m} already solved! [solve]"
  debug "SOLVE \{show m} \{show kind} lvl \{show $ length env} sp \{show sp} is \{show t}"
  let size = length $ filter (\x => x == Bound) $ toList ctx_.bds
  debug "\{show m} size is \{show size} sps \{show $ length sp}"
  let True = length sp == size
    | _ => do
      let l = length env
      debug "meta \{show m} (\{show ix}) applied to \{show $ length sp} args instead of \{show size}"
      debug "CONSTRAINT m\{show ix} \{show sp} =?= \{show t}"
      addConstraint env m sp t
  let l = length env
  debug "meta \{show meta}"
  ren <- invert l sp
  -- force unlet
  hack <- quote l t
  t <- eval env CBN hack
  catchError (do
    tm <- rename m ren l t

    let tm = lams (length sp) (reverse ctx_.boundNames) tm
    top <- get
    soln <- eval [] CBN tm

    updateMeta m $ \case
      (Unsolved pos k _ _ _ cons) => pure $ Solved pos k soln
      (Solved _ k x) => error' "Meta \{show ix} already solved! [solve2]"

    maybeCheck $ for_ cons $ \case
      MkMc fc env sp rhs => do
        val <- vappSpine soln sp
        debug "discharge l=\{show $ length env} \{(show val)} =?= \{(show rhs)}"
        unify env Normal val rhs
    mc <- readIORef top.metaCtx
    -- stack ...
    -- checkAutos ix mc.metas
    pure MkUnit
    )

    (\case
      Postpone fc ix msg => do
        -- let someone else solve this and then check again.
        debug "CONSTRAINT2 m\{show ix} \{show sp} =?= \{show t}"
        addConstraint env m sp t
      err => do
        -- I get legit errors after stuffing in solution
        -- report for now, tests aren't hitting this branch
        throwError err
        debug "CONSTRAINT3 m\{show ix} \{show sp} =?= \{show t}"
        debug "because \{showError "" err}"
        addConstraint env m sp t)

unifySpine : Env -> UnifyMode -> Bool -> SnocList Val -> SnocList Val  -> M UnifyResult
unifySpine env mode False _ _ = error emptyFC "unify failed at head" -- unreachable now
unifySpine env mode True [<] [<] = pure (MkResult [])
unifySpine env mode True (xs :< x) (ys :< y) = [| unify env mode x y <+> (unifySpine env mode True xs ys) |]
unifySpine env mode True _ _ = error emptyFC "meta spine length mismatch"


unify env mode t u = do
  debug "Unify lvl \{show $ length env}"
  debug "  \{show t}"
  debug "  =?= \{show u}"
  t' <- forceMeta t >>= unlet env
  u' <- forceMeta u >>= unlet env
  debug "forced \{show t'}"
  debug "  =?= \{show u'}"
  debug "env \{show env}"
  -- debug "types \{show $ ctx.types}"
  let l = length env
  -- On the LHS, variable matching is yields constraints/substitutions
  -- We want this to happen before VRefs are expanded, and mixing mode
  -- into the case tree explodes it further.
  case mode of
    Pattern => unifyPattern t' u'
    Normal => unifyMeta t' u'

  -- The case tree is still big here. It's hard for idris to sort
  -- What we really want is what I wrote - handle meta, handle lam, handle var, etc

  where
    -- The case tree here was huge, so I split it into stages
    -- newt will have similar issues because it doesn't emit a default case

    unifyRest : Val -> Val -> M UnifyResult
    unifyRest (VPi fc _ _ _ a b) (VPi fc' _ _ _ a' b') = do
      let fresh = VVar fc (length env) [<]
      [| unify env mode a a' <+> unify (fresh :: env) mode !(b $$ fresh) !(b' $$ fresh) |]

    unifyRest (VU _) (VU _) = pure neutral
    -- REVIEW I'd like to quote this back, but we have l that aren't in the environment.
    unifyRest t' u' = error (getFC t') "unify failed \{show t'} =?= \{show u'} \n  env is \{show env}"

    unifyRef : Val -> Val -> M UnifyResult
    unifyRef t'@(VRef fc k def sp)  u'@(VRef fc' k' def' sp') =
      -- unifySpine is a problem for cmp (S x) (S y) =?= cmp x y
        do
        -- catchError(unifySpine env mode (k == k') sp sp') $ \ err => do
            Nothing <- tryEval env t'
              | Just v => do
              debug "tryEval \{show t'} to \{show v}"
              unify env mode v u'
            Nothing <- tryEval env u'
              | Just v => unify env mode t' v
            if k == k'
              then unifySpine env mode (k == k') sp sp'
              else error fc "vref mismatch \{show t'} \{show u'}"

    -- Lennart.newt cursed type references itself
    -- We _could_ look up the ref, eval against [] and vappSpine...
    unifyRef t         u@(VRef fc' k' def sp') = do
      debug "expand \{show t} =?= %ref \{k'}"
      case lookup k' !(get) of
        Just (MkEntry _ name ty (Fn tm)) => unify env mode t !(vappSpine !(eval [] CBN tm) sp')
        _ => error fc' "unify failed \{show t} =?= \{show u} [no Fn]\n  env is \{show env}"

    unifyRef t@(VRef fc k def sp) u = do
      debug "expand %ref \{k} \{show sp} =?= \{show u}"
      case lookup k !(get) of
        Just (MkEntry _ name ty (Fn tm)) => unify env mode !(vappSpine !(eval [] CBN tm) sp) u
        _ => error fc "unify failed \{show t} [no Fn] =?= \{show u}\n  env is \{show env}"
    unifyRef t u = unifyRest t u

    unifyVar : Val -> Val -> M UnifyResult
    unifyVar t'@(VVar fc k sp)  u'@(VVar fc' k' sp')  =
      if k == k' then unifySpine env mode (k == k') sp sp'
      else error fc "Failed to unify \{show t'} and \{show u'}"

    unifyVar t'@(VVar fc k [<]) u = case !(tryEval env u) of
        Just v => unify env mode t' v
        Nothing => error fc "Failed to unify \{show t'} and \{show u}"

    unifyVar t u'@(VVar fc k [<]) = case !(tryEval env t) of
        Just v => unify env mode v u'
        Nothing => error fc "Failed to unify \{show t} and \{show u'}"
    unifyVar t u = unifyRef t u

    unifyLam : Val -> Val -> M UnifyResult
    unifyLam (VLam fc _ _ _ t)  (VLam _ _ _ _ t') = do
      let fresh = VVar fc (length env) [<]
      unify (fresh :: env) mode !(t $$ fresh) !(t' $$ fresh)
    unifyLam t         (VLam fc' _ _ _ t') = do
      debug "ETA \{show t}"
      let fresh = VVar fc' (length env) [<]
      unify (fresh :: env) mode !(t `vapp` fresh) !(t' $$ fresh)
    unifyLam (VLam fc _ _ _ t)  t'     = do
      debug "ETA' \{show t'}"
      let fresh = VVar fc (length env) [<]
      unify (fresh :: env) mode !(t $$ fresh) !(t' `vapp` fresh)
    unifyLam t u = unifyVar t u

    unifyMeta : Val -> Val -> M UnifyResult
    -- flex/flex
    unifyMeta (VMeta fc k sp) (VMeta fc' k' sp') =
      if k == k' then unifySpine env mode (k == k') sp sp'
      -- TODO, might want to try the other way, too.
      else if length sp < length sp'
        then solve env k' sp' (VMeta fc k sp) >> pure neutral
        else solve env k sp (VMeta fc' k' sp') >> pure neutral
    unifyMeta t (VMeta fc' i' sp') = solve env i' sp' t >> pure neutral
    unifyMeta (VMeta fc i sp) t' = solve env i sp t' >> pure neutral
    unifyMeta t v = unifyLam t v

    unifyPattern : Val -> Val -> M UnifyResult
    unifyPattern t'@(VVar fc k sp)  u'@(VVar fc' k' sp')  =
      if k == k' then unifySpine env mode (k == k') sp sp'
      else case (sp, sp') of
        ([<],[<]) => if k < k' then pure $ MkResult [(k,u')] else pure $ MkResult [(k',t')]
        _ => error fc "Failed to unify \{show t'} and \{show u'}"

    unifyPattern (VVar fc k [<]) u = pure $ MkResult[(k, u)]
    unifyPattern t (VVar fc k [<]) = pure $ MkResult [(k, t)]
    unifyPattern t u = unifyMeta t u


unifyCatch fc ctx ty' ty = do
    res <- catchError (unify ctx.env Normal ty' ty) $ \err => do
      let names = toList $ map fst ctx.types
      debug "fail \{show ty'} \{show ty}"
      a <- quote ctx.lvl ty'
      b <- quote ctx.lvl ty
      let msg = "unification failure: \{errorMsg err}\n  failed to unify \{pprint names a}\n             with \{pprint names b}\n  "
      throwError (E fc msg)
    case res of
      MkResult [] => pure ()
      cs => do
        -- probably want a unification mode that throws instead of returning constraints
        -- TODO need a normalizeHoles, maybe on quote?
        debug "fail with constraints \{show cs.constraints}"
        a <- quote ctx.lvl ty'
        b <- quote ctx.lvl ty
        let names = toList $ map fst ctx.types
        let msg = "xxunification failure\n  failed to unify \{pprint names a}\n             with \{pprint names b}"
        let msg = msg ++ "\nconstraints \{show cs.constraints}"
        throwError (E fc msg)
        -- error fc "Unification yields constraints \{show cs.constraints}"

export
freshMeta : Context -> FC -> Val -> MetaKind -> M Tm
freshMeta ctx fc ty kind = do
  top <- get
  mc <- readIORef top.metaCtx
  debug "fresh meta \{show mc.next} : \{show ty} (\{show kind})"
  let newmeta = Unsolved fc mc.next ctx ty kind []
  writeIORef top.metaCtx $ { next $= S, metas $= (newmeta ::) } mc
  -- infinite loop - keeps trying Ord a => Ord (a \x a)
  -- when (kind == AutoSolve) $ ignore $ trySolveAuto newmeta
  pure $ applyBDs 0 (Meta fc mc.next) ctx.bds
  where
    -- hope I got the right order here :)
    applyBDs : Nat -> Tm -> Vect k BD -> Tm
    applyBDs k t [] = t
    -- review the order here
    applyBDs k t (Bound :: xs) = App emptyFC (applyBDs (S k) t xs) (Bnd emptyFC k)
    applyBDs k t (Defined :: xs) = applyBDs (S k) t xs

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi fc x Auto rig a b => do
      m <- freshMeta ctx (getFC tm) a AutoSolve
      debug "INSERT Auto \{pprint (names ctx) m} : \{show a}"
      debug "TM \{pprint (names ctx) tm}"
      mv <- eval ctx.env CBN m
      insert ctx (App (getFC tm) tm m) !(b $$ mv)
    VPi fc x Implicit rig a b => do
      m <- freshMeta ctx (getFC tm) a Normal
      debug "INSERT \{pprint (names ctx) m} : \{show a}"
      debug "TM \{pprint (names ctx) tm}"
      mv <- eval ctx.env CBN m
      insert ctx (App (getFC tm) tm m) !(b $$ mv)
    va => pure (tm, va)

primType : FC -> QName -> M Val
primType fc nm = case lookup nm !(get) of
      Just (MkEntry _ name ty PrimTCon) => pure $ VRef fc name PrimTCon [<]
      _ => error fc "Primitive type \{show nm} not in scope"

export
infer : Context -> Raw  -> M (Tm, Val)


data Bind = MkBind String Icit Val

Show Bind where
  show (MkBind str icit x) = "\{str} \{show icit}"


---------------- Case builder

public export
record Problem where
  constructor MkProb
  clauses : List Clause
  -- I think a pi-type representing the pattern args -> goal, so we're checking
  -- We might pull out the pattern abstraction to a separate step and drop pats from clauses.
  ty : Val

-- Might have to move this if Check reaches back in...
-- this is kinda sketchy, we can't use it twice at the same depth with the same name.
fresh : {auto ctx : Context} -> String -> String
fresh base = base ++ "$" ++ show (length ctx.env)

-- The result is a casetree, but it's in Tm
export
buildTree : Context -> Problem -> M Tm

-- Updates a clause for INTRO
introClause : String -> Icit -> Clause -> M Clause
introClause nm icit (MkClause fc cons (pat :: pats) expr) =
  if icit == getIcit pat then pure $ MkClause fc ((nm, pat) :: cons) pats expr
  else if icit == Implicit then pure $ MkClause fc ((nm, PatWild fc Implicit) :: cons) (pat :: pats) expr
  else if icit == Auto then pure $ MkClause fc ((nm, PatWild fc Auto) :: cons) (pat :: pats) expr
  else error fc "Explicit arg and \{show $ getIcit pat} pattern \{show nm}  \{show pat}"
-- handle implicts at end?
introClause nm Implicit (MkClause fc cons [] expr) = pure $ MkClause fc ((nm, PatWild fc Implicit) :: cons) [] expr
introClause nm Auto (MkClause fc cons [] expr) = pure $ MkClause fc ((nm, PatWild fc Auto) :: cons) [] expr
introClause nm icit (MkClause fc cons [] expr) = error fc "Clause size doesn't match"

-- A split candidate looks like x /? Con ...
-- we need a type here. I pulled if off of the
-- pi-type, but do we need metas solved or dependents split?
-- this may dot into a dependent.
findSplit : List Constraint -> Maybe Constraint
findSplit [] = Nothing
    -- FIXME look up type, ensure it's a constructor
findSplit (x@(nm, PatCon _ _ _ _ _) :: xs) = Just x
findSplit (x@(nm, PatLit _ val) :: xs) = Just x
findSplit (x :: xs) = findSplit xs


-- ***************
-- right, I think we rewrite the names in the context before running raw and we're good to go?
-- We have stuff like S k /? x, but I think we can back up to whatever the scrutinee variable was?

-- we could pass into build case and use it for   (x /? y)

-- TODO, we may need to filter these against the type to rule out
-- impossible cases
getConstructors : Context -> FC -> Val -> M (List (QName, Nat, Tm))
getConstructors ctx scfc (VRef fc nm _ _) = do
  names <- lookupTCon nm
  traverse lookupDCon names
  where
    lookupTCon : QName -> M (List QName)
    lookupTCon str = case lookup nm !get of
        (Just (MkEntry _ name type (TCon names))) => pure names
        _ => error scfc "Not a type constructor \{nm}"
    lookupDCon : QName -> M (QName, Nat, Tm)
    lookupDCon nm = do
      case lookup nm !get of
        (Just (MkEntry _ name type (DCon k str))) => pure (name, k, type)
        Just _ => error fc "Internal Error: \{nm} is not a DCon"
        Nothing => error fc "Internal Error: DCon \{nm} not found"
getConstructors ctx scfc tm = error scfc "Can't split - not VRef: \{!(pprint ctx tm)}"

-- Extend environment with fresh variables from a pi-type
-- the pi-type here is the telescope of a constructor
-- return context, remaining type, and list of names
extendPi : Context -> Val -> SnocList Bind -> SnocList Val -> M (Context, Val, List Bind, SnocList Val)
extendPi ctx (VPi x str icit rig a b) nms sc = do
    let nm = fresh str -- "pat"
    let ctx' = extend ctx nm a
    let v = VVar emptyFC (length ctx.env) [<]
    tyb <- b $$ v
    extendPi ctx' tyb (nms :< MkBind nm icit a) (sc :< VVar x (length ctx.env) [<])
extendPi ctx ty nms sc = pure (ctx, ty, nms <>> [], sc)

-- turn vars into lets for forced values.
-- substitute inside values
-- FIXME we're not going under closures at the moment.
substVal : Nat -> Val -> Val -> Val
substVal k v tm = go tm
  where
    go : Val -> Val
    go (VVar fc j sp) = if j == k then v else (VVar fc j (map go sp))
    go (VLet fc nm a b) = VLet fc nm (go a) b
    go (VPi fc nm icit rig a b) = VPi fc nm icit rig (go a) b
    go (VMeta fc ix sp) = VMeta fc ix (map go sp)
    go (VRef fc nm y sp) = VRef fc nm y (map go sp)
    go tm = tm
    -- FIXME - do I need a Val closure like idris?
    -- or env in unify...
    -- or quote back
    -- go (VLam fc nm sc) = VLam fc nm sc
    -- go (VCase x sc xs) = ?rhs_2
    -- go (VU x) = ?rhs_7
    -- go (VLit x y) = ?rhs_8


-- need to turn k into a ground value

-- TODO rework this to do something better.  We've got constraints, and
-- and may need to do proper unification if it's already defined to a value
-- below we're handling the case if it's defined to another var, but not
-- checking for loops.
updateContext : Context -> List (Nat, Val) -> M Context
updateContext ctx [] = pure ctx
updateContext ctx ((k, val) :: cs) =
  let ix = lvl2ix (length ctx.env) k in
  case getAt ix ctx.env of
    (Just (VVar _ k' [<])) =>
      if k' /= k
        then updateContext ctx ((k',val) :: cs)
        else updateContext ({env $= map (substVal k val), bds $= replaceV ix Defined } ctx) cs
    (Just val') => do
      -- This is fine for Z =?= Z but for other stuff, we probably have to match
      info (getFC val) "need to unify \{show val} and \{show val'} or something"
      updateContext ctx cs
    Nothing => error (getFC val) "INTERNAL ERROR: bad index in updateContext"

  --
  -- updateContext ({env $= replace ix val, bds $= replaceV ix Defined } ctx) cs
  where
    replace : Nat -> Val -> List Val -> List Val
    replace k x [] = []
    replace 0 x (y :: xs) = x :: xs
    replace (S k) x (y :: xs) = y :: replace k x xs

    replaceV : Nat -> a -> Vect n a -> Vect n a
    replaceV k x [] = []
    replaceV 0 x (y :: xs) = x :: xs
    replaceV (S k) x (y :: xs) = y :: replaceV k x xs

-- ok, so this is a single constructor, CaseAlt
-- return Nothing if dcon doesn't unify with scrut
buildCase : Context -> Problem -> String -> Val -> (QName, Nat, Tm) -> M (Maybe CaseAlt)
buildCase ctx prob scnm scty (dcName, arity, ty) = do
  debug "CASE \{scnm} match \{dcName} ty \{pprint (names ctx) ty}"
  vty <- eval [] CBN ty
  (ctx', ty', vars, sc) <- extendPi ctx (vty) [<] [<]

  -- TODO I think we need to figure out what is dotted, maybe
  -- the environment manipulation below is sufficient bookkeeping
  -- or maybe it's a bad approach.

  -- At some point, I'll take a break and review more papers and code,
  -- now that I know some of the questions I'm trying to answer.

  -- We get unification constraints from matching the data constructors
  -- codomain with the scrutinee type
  debug "unify dcon cod with scrut\n  \{show ty'}\n  \{show scty}"
  Just res <- catchError(Just <$> unify ctx'.env Pattern ty' scty)
              (\err => do
                  debug "SKIP \{dcName} because unify error \{errorMsg err}"
                  pure Nothing)
    | _ => pure Nothing

  -- if the value is already constrained to a different constructor, return Nothing
  debug "scrut \{scnm} constrained to \{show $ lookupDef ctx scnm}"
  let (VRef _ sctynm _ _) = scty | _ => error (getFC scty) "case split on non-inductive \{show scty}"

  case lookupDef ctx scnm of
    Just val@(VRef fc nm y sp) =>
      if nm /= dcName
      then do
        debug "SKIP \{dcName} because \{scnm} forced to \{show val}"
        pure Nothing
      else do
        debug "case \{dcName} dotted \{show val}"
        when (length vars /= length sp) $ error emptyFC "\{show $ length vars} vars /= \{show $ length sp}"

        -- TODO - I think we need to define the context vars to sp via updateContext

        let lvl = minus (length ctx'.env) (length vars)
        let scons = constrainSpine lvl (sp <>> []) -- REVIEW is this the right order?
        ctx' <- updateContext ctx' scons

        debug "(dcon \{show dcName} ty \{show ty'} scty \{show scty}"
        debug "(dcon \{show dcName}) (vars \{show vars}) clauses were"
        for_ prob.clauses $ (\x => debug "    \{show x}")
        clauses <- mapMaybe id <$> traverse (rewriteClause sctynm vars) prob.clauses
        debug "and now:"
        for_ clauses $ (\x => debug "    \{show x}")
        when (length clauses == 0) $ error ctx.ctxFC "Missing case for \{dcName} splitting \{scnm}"
        tm <- buildTree ctx' (MkProb clauses prob.ty)
        pure $ Just $ CaseCons dcName (map getName vars) tm

    _ => do
        Right res <- tryError (unify ctx'.env Pattern ty' scty)
          | Left err => do
            debug "SKIP \{dcName} because unify error \{errorMsg err}"
            pure Nothing

        -- Constrain the scrutinee's variable to be dcon applied to args
        let Just x = findIndex ((==scnm) . fst) ctx'.types
          | Nothing => error ctx.ctxFC "\{scnm} not is scope?"
        let lvl = lvl2ix (length ctx'.env) (cast x)
        let scon : (Nat, Val) = (lvl, VRef ctx.ctxFC dcName (DCon arity dcName) sc)

        debug "scty \{show scty}"
        debug "UNIFY results \{show res.constraints}"
        debug "before types: \{show ctx'.types}"
        debug "before env: \{show ctx'.env}"
        debug "SC CONSTRAINT: \{show scon}"

        -- push the constraints into the environment by turning bind into define
        -- Is this kosher?  It might be a problem if we've already got metas over
        -- this stuff, because it intends to ignore defines.
        ctx' <- updateContext ctx' (scon :: res.constraints)

        debug "context types: \{show ctx'.types}"
        debug "context env: \{show ctx'.env}"

        -- What if all of the pattern vars are defined to meta

        debug "(dcon \{show dcName} ty \{show ty'} scty \{show scty}"
        debug "(dcon \{show dcName}) (vars \{show vars}) clauses were"
        for_ prob.clauses $ (\x => debug "    \{show x}")
        clauses <- mapMaybe id <$> traverse (rewriteClause sctynm vars) prob.clauses
        debug "and now:"
        for_ clauses $ (\x => debug "    \{show x}")
        when (length clauses == 0) $ error ctx.ctxFC "Missing case for \{dcName} splitting \{scnm}"
        tm <- buildTree ctx' (MkProb clauses prob.ty)
        pure $ Just $ CaseCons dcName (map getName vars) tm
  where
    constrainSpine : Nat -> List Val -> List (Nat, Val)
    constrainSpine lvl [] = []
    constrainSpine lvl (v :: vs) = (lvl, v) :: constrainSpine (S lvl) vs

    getName : Bind -> String
    getName (MkBind nm _ _) = nm

    -- for each clause in prob, find nm on LHS of some constraint, and
    -- "replace" with the constructor and vars.
    --
    -- This will be:
    --   x /? y    can probably just leave this
    --   x /? D a b c  split into three x /? a, y /? b, z /? c
    --   x /? E a b    drop this clause
    -- We get a list of clauses back (a Problem) and then solve that
    -- If they all fail, we have a coverage issue. (Assuming the constructor is valid)

    makeConstr : List Bind -> List Pattern -> M (List (String, Pattern))
    makeConstr [] [] = pure $ []
    makeConstr [] (pat :: pats) = error (getFC pat) "too many patterns"
    makeConstr ((MkBind nm Implicit x) :: xs) [] = pure $ (nm, PatWild emptyFC Implicit) :: !(makeConstr xs [])
    makeConstr ((MkBind nm Auto x) :: xs) [] = pure $ (nm, PatWild emptyFC Auto) :: !(makeConstr xs [])
    makeConstr ((MkBind nm Explicit x) :: xs) [] = error ctx.ctxFC "not enough patterns"
    makeConstr ((MkBind nm Explicit x) :: xs) (pat :: pats) =
      if getIcit pat == Explicit
        then pure $ (nm, pat) :: !(makeConstr xs pats)
        else error ctx.ctxFC "mismatch between Explicit and \{show $ getIcit pat}"
    makeConstr ((MkBind nm icit x) :: xs) (pat :: pats) =
      if getIcit pat /= icit -- Implicit/Explicit Implicit/Auto, etc
        then pure $ (nm, PatWild (getFC pat) icit) :: !(makeConstr xs (pat :: pats))
        else pure $ (nm, pat) :: !(makeConstr xs pats)

    -- replace constraint with constraints on parameters, or nothing if non-matching clause
    rewriteConstraint : QName -> List Bind -> List Constraint -> List Constraint -> M (Maybe (List Constraint))
    rewriteConstraint sctynm vars [] acc = pure $ Just acc
    rewriteConstraint sctynm vars (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          PatVar _ _ s => pure $ Just $ c :: (xs ++ acc)
          PatWild _ _ => pure $ Just $ c :: (xs ++ acc)
          -- FIXME why don't we hit this (when user puts 'x' for Just 'x')
          PatLit fc lit => error fc "Literal \{show lit} in constructor split"
          PatCon fc icit nm ys as => if nm == dcName
            then case as of
              Nothing => pure $ Just $ !(makeConstr vars ys) ++ xs ++ acc
              -- putting this in constraints causes it to be renamed scnm -> nm' when we check body.
              Just nm' => pure $ Just $ (scnm, (PatVar fc icit nm')) :: !(makeConstr vars ys) ++ xs ++ acc
            else do
              -- TODO can we check this when we make the PatCon?
              case lookup nm !get of
                  (Just (MkEntry _ name type (DCon k tcname))) =>
                    if (tcname /= sctynm)
                      then error fc "Constructor is \{tcname} expected \{sctynm}"
                      else pure Nothing
                  Just _ => error fc "Internal Error: \{nm} is not a DCon"
                  Nothing => error fc "Internal Error: DCon \{nm} not found"
        else rewriteConstraint sctynm vars xs (c :: acc)

    rewriteClause : QName -> List Bind -> Clause -> M (Maybe Clause)
    rewriteClause sctynm vars (MkClause fc cons pats expr) = do
      Just cons <- rewriteConstraint sctynm vars cons [] | _ => pure Nothing
      pure $ Just $ MkClause fc cons pats expr

export
splitArgs : Raw -> List (Raw, Icit) -> (Raw, List (Raw, Icit))
splitArgs (RApp fc t u icit) args = splitArgs t ((u, icit) :: args)
splitArgs tm args = (tm, args)


mkPat : TopContext -> (Raw, Icit) -> M Pattern
mkPat top (RAs fc as tm, icit) =
  case !(mkPat top (tm, icit)) of
    (PatCon fc icit nm args Nothing) => pure $ PatCon fc icit nm args (Just as)
    (PatCon fc icit nm args _) => error fc "Double as pattern \{show tm}"
    t => error fc "Can't put as on non-constructor \{show tm}"
mkPat top (tm, icit) = do
  case splitArgs tm [] of
    ((RVar fc nm), b) => case lookupRaw nm top of
                (Just (MkEntry _ name type (DCon k str))) =>
                  -- TODO check arity, also figure out why we need reverse
                  pure $ PatCon fc icit name !(traverse (mkPat top) b) Nothing
                -- This fires when a global is shadowed by a pattern var
                -- Just _ => error (getFC tm) "\{show nm} is not a data constructor"
                _ => case b of
                                [] => pure $ PatVar fc icit nm
                                _ => error (getFC tm) "patvar applied to args"
    ((RImplicit fc), []) => pure $ PatWild fc icit
    ((RImplicit fc), _) => error fc "implicit pat can't be applied to arguments"
    ((RLit fc lit), []) => pure $ PatLit fc lit
    ((RLit fc y), b) => error fc "lit cannot be applied to arguments"
    (a,b) => error (getFC a) "expected pat var or constructor, got \{show a}"


export
makeClause : TopContext -> (Raw, Raw) -> M Clause
makeClause top (lhs, rhs) = do
  let (nm, args) = splitArgs lhs []
  pats <- traverse (mkPat top) args
  pure $ MkClause (getFC lhs) [] pats rhs



-- we'll want both check and infer, we're augmenting a context
-- so probably a continuation:
-- Context -> List Decl -> (Context -> M a) -> M a
checkWhere : Context -> List Decl -> Raw -> Val -> M Tm
checkWhere ctx decls body ty = do
  -- we're going to be very proscriptive here
  let (TypeSig sigFC [name] rawtype :: decls) = decls
    | x :: _ => error (getFC x) "expected type signature"
    | _ => check ctx body ty
  funTy <- check ctx rawtype (VU sigFC)
  debug "where clause \{name} : \{pprint (names ctx) funTy}"
  let (Def defFC name' clauses :: decls') = decls
    | x :: _ => error (getFC x) "expected function definition"
    | _ => error sigFC "expected function definition after this signature"
  unless (name == name') $ error defFC "Expected def for \{name}"
  -- REVIEW is this right, cribbed from my top level code
  top <- get
  clauses' <- traverse (makeClause top) clauses
  vty <- eval ctx.env CBN funTy
  debug "\{name} vty is \{show vty}"
  let ctx' = extend ctx name vty

  -- if I lift, I need to namespace it, add args, and add args when
  -- calling locally
  -- context could hold a Name -> Val (not Tm because levels) to help with that
  -- e.g. "go" -> (VApp ... (VApp (VRef "ns.go") ...)
  -- But I'll attempt letrec first
  tm <- buildTree ({ ctxFC := defFC} ctx') (MkProb clauses' vty)
  vtm <- eval ctx'.env CBN tm
  -- Should we run the rest with the definition in place?
  -- I'm wondering if switching from bind to define will mess with metas
  -- let ctx' = define ctx name vtm vty
  pure $ LetRec sigFC name funTy tm !(checkWhere ctx' decls' body ty)


checkDone : Context -> List (String, Pattern) -> Raw -> Val -> M Tm
checkDone ctx [] body ty = do
  debug "DONE-> check body \{show body} at \{show ty}"
  -- TODO better dump context function
  debugM $ showCtx ctx
  -- Hack to try to get Combinatory working
  -- we're trying to subst in solutions here.
  env' <- for ctx.env $ \ val => do
    ty <- quote (length ctx.env) val
    -- This is not getting vars under lambdas
    eval ctx.env CBV ty
  types' <- for ctx.types $ \case
    (nm,ty) =>  do
      nty <- quote (length env') ty
      ty' <- eval env' CBV nty
      pure (nm, ty')
  let ctx = { env := env', types := types' } ctx
  debug "AFTER"
  debugM $ showCtx ctx
  -- I'm running an eval here to run case statements that are
  -- unblocked by lets in the env. (Tree.newt:cmp)
  -- The case eval code only works in the Tm -> Val case at the moment.
  -- we don't have anything like `vapp` for case
  ty <- quote (length ctx.env) ty
  ty <- eval ctx.env CBN ty

  debug "check at \{show ty}"
  got <- check ctx body ty
  debug "DONE<- got \{pprint (names ctx) got}"
  pure got
checkDone ctx ((x, PatWild _ _) :: xs) body ty = checkDone ctx xs body ty
checkDone ctx ((nm, (PatVar _ _ nm')) :: xs) body ty = checkDone ({ types $= rename } ctx) xs body ty
  where
    rename : Vect n (String, Val) -> Vect n (String, Val)
    rename [] = []
    rename ((name, ty) :: xs) =
      if name == nm
        then (nm', ty) :: xs
        else (name, ty) :: rename xs

checkDone ctx ((x, pat) :: xs) body ty = error (getFC pat) "stray constraint \{x} /? \{show pat}"

-- need to run constructors, then run default

-- wild/var can come before 'x' so we need a list first
getLits : String -> List Clause -> List Literal
getLits nm [] = []
getLits nm ((MkClause fc cons pats expr) :: cs) = case find ((nm==) . fst) cons of
  Just (_, (PatLit _ lit)) => lit :: getLits nm cs
  _ => getLits nm cs


-- then build a lit case for each of those

buildLitCase : Context -> Problem -> FC -> String -> Val -> Literal -> M CaseAlt
buildLitCase ctx prob fc scnm scty lit = do

  -- Constrain the scrutinee's variable to be lit value
  let Just ix = findIndex ((==scnm) . fst) ctx.types
    | Nothing => error ctx.ctxFC "\{scnm} not is scope?"
  let lvl = lvl2ix (length ctx.env) (cast ix)
  let scon : (Nat, Val) = (lvl, VLit fc lit)
  ctx' <- updateContext ctx [scon]
  let clauses = mapMaybe rewriteClause prob.clauses

  when (length clauses == 0) $ error ctx.ctxFC "Missing case for \{show lit} splitting \{scnm}"
  tm <- buildTree ctx' (MkProb clauses prob.ty)
  pure $ CaseLit lit tm

  where
    -- FIXME - thread in M for errors
    -- replace constraint with constraints on parameters, or nothing if non-matching clause
    rewriteConstraint : List Constraint -> List Constraint -> Maybe (List Constraint)
    rewriteConstraint [] acc = Just acc
    rewriteConstraint (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          PatVar _ _ s => Just $ c :: (xs ++ acc)
          PatWild _ _ => Just $ c :: (xs ++ acc)
          PatLit fc lit' => if lit' == lit then Just $ (xs ++ acc) else Nothing
          PatCon _ _ str ys as => Nothing -- error matching lit against constructor
        else rewriteConstraint xs (c :: acc)

    rewriteClause : Clause -> Maybe Clause
    rewriteClause (MkClause fc cons pats expr) = pure $ MkClause fc !(rewriteConstraint cons []) pats expr



buildLitCases : Context -> Problem -> FC -> String -> Val -> M (List CaseAlt)
buildLitCases ctx prob fc scnm scty = do
  let lits = nub $ getLits scnm prob.clauses
  alts <- traverse (buildLitCase ctx prob fc scnm scty) lits
  -- TODO build default case
  -- run getLits
  -- buildLitCase for each

  let defclauses = filter isDefault prob.clauses
  when (length defclauses == 0) $ error fc "no default for literal slot on \{show scnm}"
  tm <- buildTree ctx (MkProb defclauses prob.ty)

  pure $ alts ++ [ CaseDefault tm ]
  where
    isDefault : Clause -> Bool
    isDefault cl = case find ((==scnm) . fst) cl.cons of
      Just (_, (PatVar _ _ _)) => True
      Just (_, (PatWild _ _)) => True
      Nothing => True
      _ => False

-- TODO - figure out if these need to be in Prelude or have a special namespace
-- If we lookupRaw "String", we could get different answers in different contexts.
-- maybe Hardwire this one
stringType : QName
stringType = QN ["Prim"] "String"
intType = QN ["Prim"] "Int"
charType = QN ["Prim"] "Char"

litTyName : Literal -> QName
litTyName (LString str) = stringType
litTyName (LInt i) = intType
litTyName (LChar c) = charType

renameContext : String -> String -> Context -> Context
renameContext from to ctx = { types $= go } ctx
  where
    go : Vect n (String,Val) -> Vect n (String,Val)
    go Nil = Nil
    go ((a,b) :: types) = if a == from then (to,b) :: types else (a,b) :: go types

-- This process is similar to extendPi, but we need to stop
-- if one clause is short on patterns.
buildTree ctx (MkProb [] ty) = error emptyFC "no clauses"
buildTree ctx prob@(MkProb ((MkClause fc cons (x :: xs) expr) :: cs) (VPi _ str icit rig a b)) = do
  let l = length ctx.env
  let nm = fresh str -- "pat"
  let ctx' = extend ctx nm a
  -- type of the rest
  clauses <- traverse (introClause nm icit) prob.clauses
  -- REVIEW fc from a pat?
  vb <- b $$ VVar fc l [<]
  Lam fc nm icit rig <$> buildTree ctx' ({ clauses := clauses, ty := vb } prob)
buildTree ctx prob@(MkProb ((MkClause fc cons pats@(x :: xs) expr) :: cs) ty) =
  error fc "Extra pattern variables \{show pats}"
-- need to find some name we can split in (x :: xs)
-- so LHS of constraint is name (or VVar - if we do Val)
-- then run the split
-- some of this is copied into check
buildTree ctx prob@(MkProb ((MkClause fc constraints [] expr) :: cs) ty) = do
  debug "buildTree \{show constraints} \{show expr}"
  let Just (scnm, pat) = findSplit constraints
    | _ => do
      debug "checkDone \{show constraints}"
      checkDone ctx constraints expr ty

  debug "SPLIT on \{scnm} because \{show pat} \{show $ getFC pat}"
  let Just (sctm, scty) = lookupName ctx scnm
    | _ => error fc "Internal Error: can't find \{scnm} in environment"

  -- REVIEW We probably need to know this is a VRef before we decide to split on this slot..
  scty' <- unlet ctx.env scty >>= forceType ctx.env
  -- TODO attempting to pick up Autos that could have been solved immediately
  -- If we try on creation, we're looping at the moment, because of the possibility
  -- of Ord a -> Ord b -> Ord (a \x b). Need to cut earlier when solving or switch to
  -- Idris method...
  scty' <- case scty' of
    (VMeta fc1 ix sp) => do
      case !(lookupMeta ix) of
        (Solved _ k t) => forceType ctx.env scty'
        (Unsolved _ k xs _ _ _) => do
          top <- get
          mc <- readIORef top.metaCtx
          ignore $ solveAutos 0
          forceType ctx.env scty'

    _ => pure scty'

  case pat of
    PatCon fc _ _ _ as => do
      -- expand vars that may be solved, eval top level functions
      debug "EXP \{show scty} -> \{show scty'}"
      -- this is per the paper, but it would be nice to coalesce
      -- default cases
      cons <- getConstructors ctx (getFC pat) scty'
      debug "CONS \{show $ map fst cons}"
      alts <- traverse (buildCase ctx prob scnm scty') cons
      debug "GOTALTS \{show alts}"
      when (length (catMaybes alts) == 0) $ error (fc) "no alts for \{show scty'}"
      pure $ Case fc sctm (catMaybes alts)
    PatLit fc v => do
      let tyname = litTyName v
      case scty' of
        (VRef fc1 nm x sp) => when (nm /= tyname) $ error fc "expected \{show scty} and got \{tyname}"
        _ => error fc "expected \{show scty} and got \{tyname}"
      -- need to run through all of the PatLits in this slot and then find a fallback
      -- walk the list of patterns, stop if we hit a PatVar / PatWild, fail if we don't
      alts <- buildLitCases ctx prob fc scnm scty
      pure $ Case fc sctm alts
    pat => error (getFC pat) "Internal error - tried to split on \{show pat}"

showDef : Context -> List String -> Nat -> Val -> M String
showDef ctx names n v@(VVar _ n' [<]) =  if n == n' then pure "" else pure "= \{pprint names !(quote ctx.lvl v)}"
showDef ctx names n v = pure "= \{pprint names !(quote ctx.lvl v)}"

-- desugar do
undo : FC -> List DoStmt -> M Raw
undo prev [] = error prev "do block must end in expression"
undo prev ((DoExpr fc tm) :: Nil) = pure tm
-- TODO decide if we want to use >> or just >>=
undo prev ((DoExpr fc tm) :: xs) = pure $ RApp fc (RApp fc (RVar fc "_>>=_") tm Explicit) (RLam fc (BI fc "_" Explicit Many) !(undo fc xs)) Explicit
-- undo ((DoExpr fc tm) :: xs) = pure $ RApp fc (RApp fc (RVar fc "_>>_") tm Explicit) !(undo xs) Explicit
undo prev ((DoLet fc nm tm) :: xs) = RLet fc nm (RImplicit fc) tm <$> undo fc xs
undo prev ((DoArrow fc left@(RVar fc' nm) right []) :: xs) =
  case lookupRaw nm !get of
    Just _ => do
      let nm = "$sc"
      rest <- pure $ RCase fc (RVar fc nm) [MkAlt left !(undo fc xs)]
      pure $ RApp fc (RApp fc (RVar fc "_>>=_") right Explicit)
        (RLam fc (BI fc nm Explicit Many) rest) Explicit
    Nothing =>
      pure $ RApp fc (RApp fc (RVar fc "_>>=_") right Explicit)
        (RLam fc (BI fc' nm Explicit Many) !(undo fc xs)) Explicit
undo prev ((DoArrow fc left right alts) :: xs) = do
  let nm = "$sc"
  rest <- pure $ RCase fc (RVar fc nm) (MkAlt left !(undo fc xs) :: alts)
  pure $ RApp fc (RApp fc (RVar fc "_>>=_") right Explicit)
    (RLam fc (BI fc nm Explicit Many) rest) Explicit

check ctx tm ty = case (tm, !(forceType ctx.env ty)) of
  (RWhere fc decls body, ty) => checkWhere ctx (collectDecl decls) body ty
  (RIf fc a b c, ty) =>
    let tm' = RCase fc a [ MkAlt (RVar (getFC b) "True") b, MkAlt (RVar (getFC c) "False") c ] in
    check ctx tm' ty
  (RDo fc stmts, ty) => check ctx !(undo fc stmts) ty
  (RCase fc rsc alts, ty) => do
    (sc, scty) <- infer ctx rsc
    scty <- forceMeta scty
    debug "SCTM \{pprint (names ctx) sc}"
    debug "SCTY \{show scty}"

    let scnm = fresh "sc"
    top <- get
    clauses <- traverse (\(MkAlt pat rawRHS) => pure $ MkClause (getFC pat) [(scnm, !(mkPat top (pat, Explicit)))] [] rawRHS ) alts
    -- buildCase expects scrutinee to be a name in the context, so we need to let it.
    -- if it's a Bnd and not shadowed we could skip the let, but that's messy.
    let ctx' = withPos (extend ctx scnm scty) (getFC tm)
    pure $ Let fc scnm sc !(buildTree ctx' $ MkProb clauses ty)

  -- rendered in ProcessDecl
  (RHole fc, ty) => freshMeta ctx fc ty User

  (t@(RLam fc (BI _ nm icit _) tm), ty@(VPi fc' nm' icit' rig a b)) => do
          debug "icits \{nm} \{show icit} \{nm'} \{show icit'}"
          if icit == icit' then do
              let var = VVar fc (length ctx.env) [<]
              let ctx' = extend ctx nm a
              tm' <- check ctx' tm !(b $$ var)
              pure $ Lam fc nm icit rig tm'
            else if icit' /= Explicit then do
              let var = VVar fc (length ctx.env) [<]
              ty' <- b $$ var
              -- use nm' here if we want them automatically in scope
              sc <- check (extend ctx nm' a) t ty'
              pure $ Lam fc nm' icit rig sc
            else
              error fc "Icity issue checking \{show t} at \{show ty}"
  (t@(RLam _ (BI fc nm icit quant) tm), ty) =>
            error fc "Expected pi type, got \{!(prvalCtx ty)}"


  (RLet fc nm ty v sc, rty) => do
    ty' <- check ctx ty (VU emptyFC)
    vty <- eval ctx.env CBN ty'
    v' <- check ctx v vty
    vv <- eval ctx.env CBN v'
    let ctx' = define ctx nm vv vty
    sc' <- check ctx' sc rty
    pure $ Let fc nm v' sc'

  (RImplicit fc, ty) => freshMeta ctx fc ty Normal

  (tm, ty@(VPi fc nm' Implicit rig a b)) => do
    let names = toList $ map fst ctx.types
    debug "XXX edge case add implicit lambda {\{nm'} : \{show a}} to \{show tm} "
    let var = VVar fc (length ctx.env) [<]
    ty' <- b $$ var
    debugM $ pure "XXX ty' is \{!(prvalCtx {ctx=(extend ctx nm' a)} ty')}"
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam (getFC tm) nm' Implicit rig sc

  (tm, ty@(VPi fc nm' Auto rig a b)) => do
    let names = toList $ map fst ctx.types
    debug "XXX edge case add auto lambda {\{nm'} : \{show a}} to \{show tm} "
    let var = VVar fc (length ctx.env) [<]
    ty' <- b $$ var
    debugM $ pure "XXX ty' is \{!(prvalCtx {ctx=(extend ctx nm' a)} ty')}"
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam (getFC tm) nm' Auto rig sc

  (tm,ty) => do
    (tm', ty') <- infer ctx tm
    (tm', ty') <- insert ctx tm' ty'

    let names = toList $ map fst ctx.types
    debug "INFER \{show tm} to (\{pprint names tm'} : \{show ty'}) expect \{show ty}"
    unifyCatch (getFC tm) ctx ty' ty
    pure tm'

infer ctx (RVar fc nm) = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val)  -> M (Tm, Val)
    go i [] = case lookupRaw nm !(get) of
      Just (MkEntry _ name ty def) => do
        debug "lookup \{name} as \{show def}"
        pure (Ref fc name def, !(eval [] CBN ty))
      Nothing => error fc "\{show nm} not in scope"
    go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd fc i, ty)
      else go (i + 1) xs
-- FIXME tightens up output but hardcodes a name
-- infer ctx (RApp fc (RVar _ "_$_") u icit) = infer ctx u
infer ctx (RApp fc t u icit) = do
  -- If the app is explicit, add any necessary metas
  (icit, t, tty) <- case the Icit icit of
      Explicit => do
        (t, tty) <- infer ctx t
        (t, tty) <- insert ctx t tty
        pure (Explicit, t, tty)
      Implicit => do
        (t, tty) <- infer ctx t
        pure (Implicit, t, tty)
      Auto => do
        (t, tty) <- infer ctx t
        pure (Auto, t, tty)

  (a,b) <- case !(forceMeta tty) of
    (VPi fc' str icit' rig a b) => if icit' == icit then pure (a,b)
        else error fc "IcitMismatch \{show icit} \{show icit'}"

    -- If it's not a VPi, try to unify it with a VPi
    -- TODO test case to cover this.
    tty => do
      debug "unify PI for \{show tty}"
      a <- eval ctx.env CBN !(freshMeta ctx fc (VU emptyFC) Normal)
      b <- MkClosure ctx.env <$> freshMeta (extend ctx ":ins" a) fc (VU emptyFC) Normal
      -- FIXME - I had to guess Many here.  What are the side effects?
      unifyCatch fc ctx tty (VPi fc ":ins" icit Many a b)
      pure (a,b)

  u <- check ctx u a
  pure (App fc t u, !(b $$ !(eval ctx.env CBN u)))

infer ctx (RU fc) = pure (UU fc, VU fc) -- YOLO
infer ctx (RPi _ (BI fc nm icit quant) ty ty2) = do
  ty' <- check ctx ty (VU fc)
  vty' <- eval ctx.env CBN ty'
  ty2' <- check (extend ctx nm vty') ty2 (VU fc)
  pure (Pi fc nm icit quant ty' ty2', (VU fc))
infer ctx (RLet fc nm ty v sc) = do
  ty' <- check ctx ty (VU emptyFC)
  vty <- eval ctx.env CBN ty'
  v' <- check ctx v vty
  vv <- eval ctx.env CBN v'
  let ctx' = define ctx nm vv vty
  (sc',scty) <- infer ctx' sc
  pure $ (Let fc nm v' sc', scty)

infer ctx (RAnn fc tm rty) = do
  ty <- check ctx rty (VU fc)
  vty <- eval ctx.env CBN ty
  tm <- check ctx tm vty
  pure (tm, vty)

infer ctx (RLam _ (BI fc nm icit quant) tm) = do
  a <- freshMeta ctx fc (VU emptyFC) Normal >>= eval ctx.env CBN
  let ctx' = extend ctx nm a
  (tm', b) <- infer ctx' tm
  debug "make lam for \{show nm} scope \{pprint (names ctx) tm'} : \{show b}"
  pure $ (Lam fc nm icit quant tm', VPi fc nm icit quant a $ MkClosure ctx.env !(quote (S ctx.lvl) b))

infer ctx (RImplicit fc) = do
  ty <- freshMeta ctx fc (VU emptyFC) Normal
  vty <- eval ctx.env CBN ty
  tm <- freshMeta ctx fc vty Normal
  pure (tm, vty)

infer ctx (RLit fc (LString str)) = pure (Lit fc (LString str), !(primType fc stringType))
infer ctx (RLit fc (LInt i)) = pure (Lit fc (LInt i), !(primType fc intType))
infer ctx (RLit fc (LChar c)) = pure (Lit fc (LChar c), !(primType fc charType))
infer ctx (RAs fc _ _) = error fc "@ can only be used in patterns"
infer ctx tm = error (getFC tm) "Implement infer \{show tm}"

module Lib.Elab

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Control.Monad.Identity
import Lib.Parser.Impl
import Lib.Prettier
import Data.List
import Data.Vect
import Data.String
import Data.IORef
import Lib.Types
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

-- We need to switch to SortedMap here
export
updateMeta : Nat -> (MetaEntry -> M MetaEntry) -> M ()
updateMeta ix f = do
  top <- get
  mc <- readIORef top.metas
  metas <- go mc.metas
  writeIORef top.metas $ {metas := metas} mc
  where
    go : List MetaEntry -> M (List MetaEntry)
    go [] = error' "Meta \{show ix} not found"
    go (x@((Unsolved y k z w v ys)) :: xs) = if k == ix then (::xs) <$> f x else (x ::) <$> go xs
    go (x@((Solved _ k y)) :: xs) = if k == ix then (::xs) <$> f x else (x ::) <$> go xs

export
addConstraint : Env -> Nat -> SnocList Val -> Val -> M ()
addConstraint env ix sp tm = do
  top <- get
  mc <- readIORef top.metas
  updateMeta ix $ \case
    (Unsolved pos k a b c cons) => do
      debug "Add constraint m\{show ix} \{show sp} =?= \{show tm}"
      pure (Unsolved pos k a b c (MkMc (getFC tm) env sp tm :: cons))
    (Solved _ k tm) => error' "Meta \{show k} already solved"
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
rename : Nat -> List Nat -> Nat -> Val  -> M  Tm
rename meta ren lvl v = go ren lvl v
  where
    go : List Nat -> Nat -> Val  -> M  Tm
    goSpine : List Nat -> Nat -> Tm -> SnocList Val  -> M Tm
    goSpine ren lvl tm [<] = pure tm
    goSpine ren lvl tm (xs :< x) = do
      xtm <- go ren lvl x
      pure $ App emptyFC !(goSpine ren lvl tm xs) xtm

    go ren lvl (VVar fc k sp) = case findIndex (== k) ren of
      Nothing => error fc "scope/skolem thinger VVar \{show k} ren \{show ren}"
      Just x => goSpine ren lvl (Bnd fc $ cast x) sp
    go ren lvl (VRef fc nm def sp) = goSpine ren lvl (Ref fc nm def) sp
    go ren lvl (VMeta fc ix sp) = do
      -- So sometimes we have an unsolved meta in here which reference vars out of scope.
      debug "rename Meta \{show ix} spine \{show sp}"
      if ix == meta
      -- REVIEW is this the right fc?
        then error fc "meta occurs check"
        else case !(lookupMeta ix) of
          Solved fc _ val => do
            debug "rename: \{show ix} is solved"
            go ren lvl !(vappSpine val sp)
          _ => do
            debug "rename: \{show ix} is unsolved"
            catchError {e=Error} (goSpine ren lvl (Meta fc ix) sp) (\err => throwError $ Postpone fc ix (errorMsg err))
    go ren lvl (VLam fc n t) = pure (Lam fc n !(go (lvl :: ren) (S lvl) !(t $$ VVar fc lvl [<])))
    go ren lvl (VPi fc n icit ty tm) = pure (Pi fc n icit !(go ren lvl ty) !(go (lvl :: ren) (S lvl) !(tm $$ VVar emptyFC lvl [<])))
    go ren lvl (VU fc) = pure (U fc)
    -- for now, we don't do solutions with case in them.
    go ren lvl (VCase fc sc alts) = error fc "Case in solution"
    go ren lvl (VLit fc lit) = pure (Lit fc lit)
    go ren lvl (VLet fc name val body) =
      pure $ Let fc name !(go ren lvl val) !(go (lvl :: ren) (S lvl) body)
    go ren lvl (VLetRec fc name val body) =
      pure $ Let fc name !(go (lvl :: ren) (S lvl) val) !(go (lvl :: ren) (S lvl) body)

lams : Nat -> List String -> Tm -> Tm
lams 0 _ tm = tm
lams (S k) [] tm = Lam emptyFC "arg_\{show k}" (lams k [] tm)
lams (S k) (x :: xs) tm = Lam emptyFC x (lams k xs tm)

export
unify : Env -> UnifyMode -> Val -> Val  -> M UnifyResult

(.boundNames) : Context -> List String
ctx.boundNames = map snd $ filter (\x => fst x == Bound) $ toList $ zip ctx.bds (map fst ctx.types)

export
solve : Env -> (k : Nat) -> SnocList Val -> Val -> M  ()
solve env m sp t = do
  meta@(Unsolved metaFC ix ctx_ ty kind cons) <- lookupMeta m
    | _ => error (getFC t) "Meta \{show m} already solved!"
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
  catchError {e=Error} (do
    tm <- rename m ren l t

    let tm = lams (length sp) (reverse ctx_.boundNames) tm
    top <- get
    soln <- eval [] CBN tm

    updateMeta m $ \case
      (Unsolved pos k _ _ _ cons) => pure $ Solved pos k soln
      (Solved _ k x) => error' "Meta \{show ix} already solved!"
    for_ cons $ \case
      MkMc fc env sp rhs => do
        val <- vappSpine soln sp
        debug "discharge l=\{show $ length env} \{(show val)} =?= \{(show rhs)}"
        unify env Normal val rhs)
    (\case
      Postpone fc ix msg => do
        -- let someone else solve this and then check again.
        debug "CONSTRAINT2 m\{show ix} \{show sp} =?= \{show t}"
        addConstraint env m sp t
      err => do
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
    Normal => unify' t' u'

  -- The case tree is still big here. It's hard for idris to sort
  -- What we really want is what I wrote - handle meta, handle lam, handle var, etc

  where
    unify' : Val -> Val -> M UnifyResult
    -- flex/flex
    unify' (VMeta fc k sp) (VMeta fc' k' sp') =
      if k == k' then unifySpine env mode (k == k') sp sp'
      -- TODO, might want to try the other way, too.
      else if length sp < length sp'
        then solve env k' sp' (VMeta fc k sp) >> pure neutral
        else solve env k sp (VMeta fc' k' sp') >> pure neutral
    unify' t (VMeta fc' i' sp') = solve env i' sp' t >> pure neutral
    unify' (VMeta fc i sp) t' = solve env i sp t' >> pure neutral
    unify' (VPi fc _ _ a b) (VPi fc' _ _ a' b') = do
      let fresh = VVar fc (length env) [<]
      [| unify env mode a a' <+> unify (fresh :: env) mode !(b $$ fresh) !(b' $$ fresh) |]

    -- we don't eta expand on LHS
    unify' (VLam fc _ t)  (VLam _ _ t') = do
      let fresh = VVar fc (length env) [<]
      unify (fresh :: env) mode !(t $$ fresh) !(t' $$ fresh)
    unify' t         (VLam fc' _ t') = do
      debug "ETA \{show t}"
      let fresh = VVar fc' (length env) [<]
      unify (fresh :: env) mode !(t `vapp` fresh) !(t' $$ fresh)
    unify' (VLam fc _ t)  t'     = do
      debug "ETA' \{show t'}"
      let fresh = VVar fc (length env) [<]
      unify (fresh :: env) mode !(t $$ fresh) !(t' `vapp` fresh)

    unify' t'@(VVar fc k sp)  u'@(VVar fc' k' sp')  =
      if k == k' then unifySpine env mode (k == k') sp sp'
      else error fc "Failed to unify \{show t'} and \{show u'}"

    unify' t'@(VVar fc k [<]) u = case !(tryEval env u) of
        Just v => unify env mode t' v
        Nothing => error fc "Failed to unify \{show t'} and \{show u}"

    unify' t u'@(VVar fc k [<]) = case !(tryEval env t) of
        Just v => unify env mode v u'
        Nothing => error fc "Failed to unify \{show t} and \{show u'}"

    -- REVIEW - consider separate value for DCon/TCon
    unify' t'@(VRef fc k def sp)  u'@(VRef fc' k' def' sp') =
      -- unifySpine is a problem for cmp (S x) (S y) =?= cmp x y
        do
        -- catchError {e = Error} (unifySpine env mode (k == k') sp sp') $ \ err => do
            Nothing <- tryEval env t'
              | Just v => do
              debug "tryEval \{show t'} to \{show v}"
              unify env mode v u'
            Nothing <- tryEval env u'
              | Just v => unify env mode t' v
            if k == k'
              then unifySpine env mode (k == k') sp sp'
              else error fc "vref mismatch \{show t'} \{show u'}"

    unify' (VU _) (VU _) = pure neutral
    -- Lennart.newt cursed type references itself
    -- We _could_ look up the ref, eval against [] and vappSpine...
    unify' t         u@(VRef fc' k' def sp') = do
      debug "expand \{show t} =?= %ref \{k'}"
      case lookup k' !(get) of
        Just (MkEntry name ty (Fn tm)) => unify env mode t !(vappSpine !(eval [] CBN tm) sp')
        _ => error fc' "unify failed \{show t} =?= \{show u} [no Fn]\n  env is \{show env}"

    unify' t@(VRef fc k def sp) u = do
      debug "expand %ref \{k} \{show sp} =?= \{show u}"
      case lookup k !(get) of
        Just (MkEntry name ty (Fn tm)) => unify env mode !(vappSpine !(eval [] CBN tm) sp) u
        _ => error fc "unify failed \{show t} [no Fn] =?= \{show u}\n  env is \{show env}"

    -- REVIEW I'd like to quote this back, but we have l that aren't in the environment.
    unify' t' u' = error (getFC t') "unify failed \{show t'} =?= \{show u'} \n  env is \{show env}"

    unifyPattern : Val -> Val -> M UnifyResult
    unifyPattern t'@(VVar fc k sp)  u'@(VVar fc' k' sp')  =
      if k == k' then unifySpine env mode (k == k') sp sp'
      else case (sp, sp') of
        ([<],[<]) => if k < k' then pure $ MkResult [(k,u')] else pure $ MkResult [(k',t')]
        _ => error fc "Failed to unify \{show t'} and \{show u'}"

    unifyPattern (VVar fc k [<]) u = pure $ MkResult[(k, u)]
    unifyPattern t (VVar fc k [<]) = pure $ MkResult [(k, t)]
    unifyPattern t u = unify' t u

export
unifyCatch : FC -> Context -> Val -> Val -> M ()
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
        let msg = "unification failure\n  failed to unify \{pprint names a}\n             with \{pprint names b}"
        let msg = msg ++ "\nconstraints \{show cs.constraints}"
        throwError (E fc msg)
        -- error fc "Unification yields constraints \{show cs.constraints}"

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi fc x Auto a b => do
      -- FIXME mark meta as auto, maybe try to solve here?
      m <- freshMeta ctx (getFC tm) a AutoSolve
      debug "INSERT Auto \{pprint (names ctx) m} : \{show a}"
      debug "TM \{pprint (names ctx) tm}"
      mv <- eval ctx.env CBN m
      insert ctx (App (getFC tm) tm m) !(b $$ mv)
    VPi fc x Implicit a b => do
      m <- freshMeta ctx (getFC tm) a Normal
      debug "INSERT \{pprint (names ctx) m} : \{show a}"
      debug "TM \{pprint (names ctx) tm}"
      mv <- eval ctx.env CBN m
      insert ctx (App (getFC tm) tm m) !(b $$ mv)
    va => pure (tm, va)

primType : FC -> String -> M Val
primType fc nm = case lookup nm !(get) of
      Just (MkEntry name ty PrimTCon) => pure $ VRef fc name PrimTCon [<]
      _ => error fc "Primitive type \{show nm} not in scope"

export
infer : Context -> Raw  -> M  (Tm, Val)

export
check : Context -> Raw -> Val  -> M  Tm

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
findSplit (x@(nm, PatCon _ _ cnm pats) :: xs) = Just x
findSplit (x@(nm, PatLit _ val) :: xs) = Just x
findSplit (x :: xs) = findSplit xs


-- ***************
-- right, I think we rewrite the names in the context before running raw and we're good to go?
-- We have stuff like S k /? x, but I think we can back up to whatever the scrutinee variable was?

-- we could pass into build case and use it for   (x /? y)

-- TODO, we may need to filter these against the type to rule out
-- impossible cases
getConstructors : Context -> FC -> Val -> M (List (String, Nat, Tm))
getConstructors ctx scfc (VRef fc nm _ _) = do
  names <- lookupTCon nm
  traverse lookupDCon names
  where
    lookupTCon : String -> M (List String)
    lookupTCon str = case lookup nm !get of
        (Just (MkEntry name type (TCon names))) => pure names
        _ => error scfc "Not a type constructor \{nm}"
    lookupDCon : String -> M (String, Nat, Tm)
    lookupDCon nm = do
      case lookup nm !get of
        (Just (MkEntry name type (DCon k str))) => pure (name, k, type)
        Just _ => error fc "Internal Error: \{nm} is not a DCon"
        Nothing => error fc "Internal Error: DCon \{nm} not found"
getConstructors ctx scfc tm = error scfc "Can't split - not VRef: \{!(pprint ctx tm)}"

-- Extend environment with fresh variables from a pi-type
-- the pi-type here is the telescope of a constructor
-- return context, remaining type, and list of names
extendPi : Context -> Val -> SnocList Bind -> SnocList Val -> M (Context, Val, List Bind, SnocList Val)
extendPi ctx (VPi x str icit a b) nms sc = do
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
    go (VPi fc nm icit a b) = VPi fc nm icit (go a) b
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


updateContext : Context -> List (Nat, Val) -> M Context
updateContext ctx [] = pure ctx
updateContext ctx ((k, val) :: cs) = let ix = (length ctx.env `minus` k) `minus` 1 in
  updateContext ({env $= map (substVal k val), bds $= replaceV ix Defined } ctx) cs
  -- updateContext ({env $= replace ix val, bds $= replaceV ix Defined } ctx) cs
  where
    replace : Nat -> a -> List a -> List a
    replace k x [] = []
    replace 0 x (y :: xs) = x :: xs
    replace (S k) x (y :: xs) = y :: replace k x xs

    replaceV : Nat -> a -> Vect n a -> Vect n a
    replaceV k x [] = []
    replaceV 0 x (y :: xs) = x :: xs
    replaceV (S k) x (y :: xs) = y :: replaceV k x xs

forcedName : Context -> String -> Maybe Name
forcedName ctx nm = case lookupName ctx nm of
  Just (Bnd fc ix, ty) => case getAt ix ctx.env of
    (Just (VRef x nm y sp)) => -- TODO verify is constructor?
      Just nm
    _ => Nothing
  _ => Nothing

-- ok, so this is a single constructor, CaseAlt
-- return Nothing if dcon doesn't unify with scrut
buildCase : Context -> Problem -> String -> Val -> (String, Nat, Tm) -> M (Maybe CaseAlt)
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
  Just res <- catchError {e = Error} (Just <$> unify ctx'.env Pattern ty' scty)
              (\err => do
                  debug "SKIP \{dcName} because unify error \{errorMsg err}"
                  pure Nothing)
    | _ => pure Nothing

  -- if the value is already constrained to a different constructor, return Nothing
  debug "scrut \{scnm} constrained to \{show $ lookupDef ctx scnm}"

  case lookupDef ctx scnm of
    Just val@(VRef fc nm y sp) =>
      if nm /= dcName
      then do
        debug "SKIP \{dcName} because \{scnm} forced to \{show val}"
        pure Nothing
      else do
        debug "DOTTED \{dcName} \{show val}"

        -- TODO - I think we need to define the context vars to sp via updateContext

        debug "(dcon \{show dcName} ty \{show ty'} scty \{show scty}"
        debug "(dcon \{show dcName}) (vars \{show vars}) clauses were"
        for_ prob.clauses $ (\x => debug "    \{show x}")
        let clauses = mapMaybe (rewriteClause vars) prob.clauses
        debug "and now:"
        for_ clauses $ (\x => debug "    \{show x}")
        when (length clauses == 0) $ error ctx.fc "Missing case for \{dcName} splitting \{scnm}"
        tm <- buildTree ctx' (MkProb clauses prob.ty)
        pure $ Just $ CaseCons dcName (map getName vars) tm

    _ => do
        Right res <- tryError {e = Error} (unify ctx'.env Pattern ty' scty)
          | Left err => do
            debug "SKIP \{dcName} because unify error \{errorMsg err}"
            pure Nothing

        -- Constrain the scrutinee's variable to be dcon applied to args
        let Just x = findIndex ((==scnm) . fst) ctx'.types
          | Nothing => error ctx.fc "\{scnm} not is scope?"
        let lvl = ((length ctx'.env) `minus` (cast x)) `minus` 1
        let scon : (Nat, Val) = (lvl, VRef ctx.fc dcName (DCon arity dcName) sc)

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
        let clauses = mapMaybe (rewriteClause vars) prob.clauses
        debug "and now:"
        for_ clauses $ (\x => debug "    \{show x}")
        when (length clauses == 0) $ error ctx.fc "Missing case for \{dcName} splitting \{scnm}"
        tm <- buildTree ctx' (MkProb clauses prob.ty)
        pure $ Just $ CaseCons dcName (map getName vars) tm
  where
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

    makeConstr : List Bind -> List Pattern -> List (String, Pattern)
    makeConstr [] [] = []
    -- would need M in here to throw, and I'm building stuff as I go, I suppose I could <$>
    makeConstr [] (pat :: pats) = ?extra_patterns
    makeConstr ((MkBind nm Implicit x) :: xs) [] = (nm, PatWild emptyFC Implicit) :: makeConstr xs []
    makeConstr ((MkBind nm Auto x) :: xs) [] = (nm, PatWild emptyFC Auto) :: makeConstr xs []
    -- FIXME need a proper error, but requires wiring M three levels down
    makeConstr ((MkBind nm Explicit x) :: xs) [] = ?insufficient_patterns
    makeConstr ((MkBind nm Explicit x) :: xs) (pat :: pats) =
      if getIcit pat == Explicit
        then (nm, pat) :: makeConstr xs pats
        else ?explict_implicit_mismatch
    makeConstr ((MkBind nm icit x) :: xs) (pat :: pats) =
      if getIcit pat /= icit -- Implicit/Explicit Implicit/Auto, etc
        then (nm, PatWild (getFC pat) icit) :: makeConstr xs (pat :: pats)
        else (nm, pat) :: makeConstr xs pats

    -- replace constraint with constraints on parameters, or nothing if non-matching clause
    rewriteConstraint : List Bind -> List Constraint -> List Constraint -> Maybe (List Constraint)
    rewriteConstraint vars [] acc = Just acc
    rewriteConstraint vars (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          PatVar _ _ s => Just $ c :: (xs ++ acc)
          PatWild _ _ => Just $ c :: (xs ++ acc)
          PatLit fc lit => Nothing -- error fc "Literal \{show lit} in constructor split"
          PatCon _ _ str ys => if str == dcName
            then Just $ (makeConstr vars ys) ++ xs ++ acc
            else Nothing
        else rewriteConstraint vars xs (c :: acc)

    rewriteClause : List Bind -> Clause -> Maybe Clause
    rewriteClause vars (MkClause fc cons pats expr) = pure $ MkClause fc !(rewriteConstraint vars cons []) pats expr


splitArgs : Raw -> List (Raw, Icit) -> (Raw, List (Raw, Icit))
splitArgs (RApp fc t u icit) args = splitArgs t ((u, icit) :: args)
splitArgs tm args = (tm, args)


mkPat : TopContext -> (Raw, Icit) -> M Pattern
mkPat top (tm, icit) = do
  case splitArgs tm [] of
    ((RVar fc nm), b) => case lookup nm top of
                (Just (MkEntry name type (DCon k str))) =>
                  -- TODO check arity, also figure out why we need reverse
                  pure $ PatCon fc icit nm !(traverse (mkPat top) b)
                -- This fires when a global is shadowed by a pattern var
                -- Just _ => error (getFC tm) "\{show nm} is not a data constructor"
                _ => case b of
                                [] => pure $ PatVar fc icit nm
                                _ => error (getFC tm) "patvar applied to args"
    ((RImplicit fc), []) => pure $ PatWild fc icit
    ((RImplicit fc), _) => error fc "implicit pat can't be applied to arguments"
    ((RLit fc lit), []) => pure $ PatLit fc lit
    ((RLit fc y), b) => error fc "lit cannot be applied to arguments"
    (a,b) => error (getFC a) "expected pat var or constructor"


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
  tm <- buildTree ctx' (MkProb clauses' vty)
  vtm <- eval ctx'.env CBN tm
  -- Should we run the rest with the definition in place?
  -- I'm wondering if switching from bind to define will mess with metas
  -- let ctx' = define ctx name vtm vty
  pure $ LetRec sigFC name tm !(checkWhere ctx' decls' body ty)


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
    | Nothing => error ctx.fc "\{scnm} not is scope?"
  let lvl = ((length ctx.env) `minus` (cast ix)) `minus` 1
  let scon : (Nat, Val) = (lvl, VLit fc lit)
  ctx' <- updateContext ctx [scon]
  let clauses = mapMaybe rewriteClause prob.clauses

  when (length clauses == 0) $ error ctx.fc "Missing case for \{show lit} splitting \{scnm}"
  tm <- buildTree ctx' (MkProb clauses prob.ty)
  pure $ CaseLit lit tm

  where
    -- replace constraint with constraints on parameters, or nothing if non-matching clause
    rewriteConstraint : List Constraint -> List Constraint -> Maybe (List Constraint)
    rewriteConstraint [] acc = Just acc
    rewriteConstraint (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          PatVar _ _ s => Just $ c :: (xs ++ acc)
          PatWild _ _ => Just $ c :: (xs ++ acc)
          PatLit fc lit' => if lit' == lit then Just $ (xs ++ acc) else Nothing
          PatCon _ _ str ys => Nothing -- error matching lit against constructor
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


-- This process is similar to extendPi, but we need to stop
-- if one clause is short on patterns.
buildTree ctx (MkProb [] ty) = error emptyFC "no clauses"
buildTree ctx prob@(MkProb ((MkClause fc cons (x :: xs) expr) :: cs) (VPi _ str icit a b)) = do
  let l = length ctx.env
  let nm = fresh str -- "pat"
  let ctx' = extend ctx nm a
  -- type of the rest
  clauses <- traverse (introClause nm icit) prob.clauses
  -- REVIEW fc from a pat?
  vb <- b $$ VVar fc l [<]
  Lam fc nm <$> buildTree ctx' ({ clauses := clauses, ty := vb } prob)
buildTree ctx prob@(MkProb ((MkClause fc cons pats@(x :: xs) expr) :: cs) ty) =
  error fc "Extra pattern variables \{show pats}"
-- need to find some name we can split in (x :: xs)
-- so LHS of constraint is name (or VVar - if we do Val)
-- then run the split
-- some of this is copied into check
buildTree ctx prob@(MkProb ((MkClause fc constraints [] expr) :: cs) ty) = do
  debug "buildTree \{show constraints} \{show expr}"
  let Just (scnm, pat) := findSplit constraints
    | _ => do
      debug "checkDone \{show constraints}"
      checkDone ctx constraints expr ty

  debug "SPLIT on \{scnm} because \{show pat} \{show $ getFC pat}"
  let Just (sctm, scty) := lookupName ctx scnm
    | _ => error fc "Internal Error: can't find \{scnm} in environment"

  case pat of
    PatCon _ _ _ _ => do
      -- expand vars that may be solved, eval top level functions
      scty' <- unlet ctx.env scty >>= forceType ctx.env
      debug "EXP \{show scty} -> \{show scty'}"
      -- this is per the paper, but it would be nice to coalesce
      -- default cases
      cons <- getConstructors ctx (getFC pat) scty'
      debug "CONS \{show $ map fst cons}"
      alts <- traverse (buildCase ctx prob scnm scty) cons
      debug "GOTALTS \{show alts}"
      when (length (catMaybes alts) == 0) $ error (fc) "no alts for \{show scty'}"
      -- TODO check for empty somewhere?
      pure $ Case fc sctm (catMaybes alts)
    PatLit fc v => do
      -- need to run through all of the PatLits in this slot and then find a fallback
      -- walk the list of patterns, stop if we hit a PatVar / PatWild, fail if we don't
      alts <- buildLitCases ctx prob fc scnm scty
      pure $ Case fc sctm alts
    pat => error (getFC pat) "Internal error - tried to split on \{show pat}"

showDef : Context -> List String -> Nat -> Val -> M String
showDef ctx names n v@(VVar _ n' [<]) =  if n == n' then pure "" else pure "= \{pprint names !(quote ctx.lvl v)}"
showDef ctx names n v = pure "= \{pprint names !(quote ctx.lvl v)}"


undo : List DoStmt -> M Raw
undo [] = error emptyFC "do block must end in expression"
undo ((DoExpr fc tm) :: Nil) = pure tm
-- TODO decide if we want to use >> or just >>=
undo ((DoExpr fc tm) :: xs) = pure $ RApp fc (RApp fc (RVar fc "_>>=_") tm Explicit) (RLam fc (BI fc "_" Explicit Many) !(undo xs)) Explicit
-- undo ((DoExpr fc tm) :: xs) = pure $ RApp fc (RApp fc (RVar fc "_>>_") tm Explicit) !(undo xs) Explicit
undo ((DoLet fc nm tm) :: xs) = RLet fc nm (RImplicit fc) tm <$> undo xs
undo ((DoArrow fc nm tm) :: xs) = pure $ RApp fc (RApp fc (RVar fc "_>>=_") tm Explicit) (RLam fc (BI fc nm Explicit Many) !(undo xs)) Explicit

check ctx tm ty = case (tm, !(forceType ctx.env ty)) of
  (RWhere fc decls body, ty) => checkWhere ctx (collectDecl decls) body ty
  (RIf fc a b c, ty) =>
    let tm' = RCase fc a [ MkAlt (RVar (getFC b) "True") b, MkAlt (RVar (getFC c) "False") c ] in
    check ctx tm' ty
  (RDo fc stmts, ty) => check ctx !(undo stmts) ty
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
    let ctx' = extend ctx scnm scty
    pure $ Let fc scnm sc !(buildTree ctx' $ MkProb clauses ty)

  -- rendered in ProcessDecl
  (RHole fc, ty) => freshMeta ctx fc ty User

  (t@(RLam fc (BI _ nm icit _) tm), ty@(VPi fc' nm' icit' a b)) => do
          debug "icits \{nm} \{show icit} \{nm'} \{show icit'}"
          if icit == icit' then do
              let var = VVar fc (length ctx.env) [<]
              let ctx' = extend ctx nm a
              tm' <- check ctx' tm !(b $$ var)
              pure $ Lam fc nm tm'
            else if icit' /= Explicit then do
              let var = VVar fc (length ctx.env) [<]
              ty' <- b $$ var
              -- use nm' here if we want them automatically in scope
              sc <- check (extend ctx nm' a) t ty'
              pure $ Lam fc nm' sc
            else
              error fc "Icity issue checking \{show t} at \{show ty}"
  (t@(RLam _ (BI fc nm icit quant) tm), ty) =>
            error fc "Expected pi type, got \{!(prvalCtx ty)}"

  (tm, ty@(VPi fc nm' Implicit a b)) => do
    let names = toList $ map fst ctx.types
    debug "XXX edge case add implicit lambda {\{nm'} : \{show a}} to \{show tm} "
    let var = VVar fc (length ctx.env) [<]
    ty' <- b $$ var
    debugM $ pure "XXX ty' is \{!(prvalCtx {ctx=(extend ctx nm' a)} ty')}"
    sc <- check (extend ctx nm' a) tm ty'
    pure $ Lam (getFC tm) nm' sc

  (RImplicit fc, ty) => freshMeta ctx fc ty Normal

  (RLet fc nm ty v sc, rty) => do
    ty' <- check ctx ty (VU emptyFC)
    vty <- eval ctx.env CBN ty'
    v' <- check ctx v vty
    vv <- eval ctx.env CBN v'
    let ctx' = define ctx nm vv vty
    sc' <- check ctx' sc rty
    pure $ Let fc nm v' sc'

  (tm,ty) => do
    -- We need to insert if tm is not an Implicit Lam
    -- assuming all of the implicit ty have been handled above
    let names = toList $ map fst ctx.types
    (tm', ty') <- case !(infer ctx tm) of
      -- Kovacs doesn't insert on tm = Implicit Lam, we don't have Plicity in Lam
      -- so I'll check the inferred type for an implicit pi
      -- This seems wrong, the ty' is what insert runs on, so we're just short circuiting here
      (tm'@(Lam{}), ty'@(VPi _ _ Implicit _ _)) => do debug "CheckMe 1"; pure (tm', ty')
      (tm'@(Lam{}), ty'@(VPi _ _ Auto _ _)) => do debug "CheckMe 2"; pure (tm', ty')
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
    (VPi fc str icit' a b) => if icit' == icit then pure (a,b)
        else error fc "IcitMismatch \{show icit} \{show icit'}"

    -- If it's not a VPi, try to unify it with a VPi
    -- TODO test case to cover this.
    tty => do
      debug "unify PI for \{show tty}"
      a <- eval ctx.env CBN !(freshMeta ctx fc (VU emptyFC) Normal)
      b <- MkClosure ctx.env <$> freshMeta (extend ctx ":ins" a) fc (VU emptyFC) Normal
      unifyCatch fc ctx tty (VPi fc ":ins" icit a b)
      pure (a,b)

  u <- check ctx u a
  pure (App fc t u, !(b $$ !(eval ctx.env CBN u)))

infer ctx (RU fc) = pure (U fc, VU fc) -- YOLO
infer ctx (RPi _ (BI fc nm icit quant) ty ty2) = do
  ty' <- check ctx ty (VU fc)
  vty' <- eval ctx.env CBN ty'
  ty2' <- check (extend ctx nm vty') ty2 (VU fc)
  pure (Pi fc nm icit ty' ty2', (VU fc))
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
  pure $ (Lam fc nm tm', VPi fc nm icit a $ MkClosure ctx.env !(quote (S ctx.lvl) b))
  -- error {ctx} [DS "can't infer lambda"]

infer ctx (RImplicit fc) = do
  ty <- freshMeta ctx fc (VU emptyFC) Normal
  vty <- eval ctx.env CBN ty
  tm <- freshMeta ctx fc vty Normal
  pure (tm, vty)

infer ctx (RLit fc (LString str)) = pure (Lit fc (LString str), !(primType fc "String"))
infer ctx (RLit fc (LInt i)) = pure (Lit fc (LInt i), !(primType fc "Int"))
infer ctx (RLit fc (LChar c)) = pure (Lit fc (LChar c), !(primType fc "Char"))

infer ctx tm = error (getFC tm) "Implement infer \{show tm}"

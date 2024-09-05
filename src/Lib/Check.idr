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


public export
record UnifyResult where
  constructor MkResult
  -- wild guess here - lhs is a VVar
  constraints : List (Nat, Val)

Semigroup UnifyResult where
  (MkResult cs) <+> (MkResult cs') = MkResult (cs ++ cs')

Monoid UnifyResult where
  neutral = MkResult []

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

  export
  unify : (l : Nat) -> Val -> Val  -> M UnifyResult

  unifySpine : Nat -> Bool -> SnocList Val -> SnocList Val  -> M UnifyResult
  unifySpine l False _ _ = error emptyFC "unify failed at head" -- unreachable now
  unifySpine l True [<] [<] = pure (MkResult [])
  unifySpine l True (xs :< x) (ys :< y) = [| unify l x y <+> (unifySpine l True xs ys) |]
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
    debug "types \{show $ ctx.types}"
    case (t',u') of
      (VLam _ _ t,  VLam _ _ t') => unify (l + 1) !(t $$ VVar emptyFC l [<]) !(t' $$ VVar emptyFC l [<])
      (t,         VLam fc' _ t') => unify (l + 1) !(t `vapp` VVar emptyFC l [<]) !(t' $$ VVar emptyFC l [<])
      (VLam fc _ t,  t'       ) => unify (l + 1) !(t $$ VVar emptyFC l [<]) !(t' `vapp` VVar emptyFC l [<])
      (VPi fc _ _ a b, VPi fc' _ _ a' b') => [| unify l a a' <+> unify (S l) !(b $$ VVar emptyFC l [<]) !(b' $$ VVar emptyFC l [<]) |]
      (VVar fc k sp,   VVar fc' k' sp'  ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else error emptyFC "vvar mismatch \{show k} \{show k'}"

      -- attempt at building constraints
      -- and using them
      (VVar fc k sp, u) => case lookupVar k of
        Just v => unify l v u
        Nothing => pure $ MkResult[(k, u)]
      (t, VVar fc k sp) => pure $ MkResult[(k, t)]

      (VRef fc k def sp,   VRef fc' k' def' sp'  ) =>
        if k == k' then do
          debug "unify \{show l} spine at \{k} \{show sp} \{show sp'}"
          unifySpine l (k == k') sp sp'
        -- REVIEW - consider forcing?
        else error emptyFC "vref mismatch \{show k} \{show k'} -- \{show sp} \{show sp'}"

      (VMeta fc k sp,  VMeta fc' k' sp' ) =>
        if k == k' then unifySpine l (k == k') sp sp'
        else solve l k sp (VMeta fc' k' sp') >> pure neutral
      (t,           VMeta fc' i' sp') => solve l i' sp' t >> pure neutral
      (VMeta fc i sp, t'           ) => solve l i sp t' >> pure neutral
      (VU _, VU _) => pure neutral
      -- Lennart.newt cursed type references itself
      -- We _could_ look up the ref, eval against [] and vappSpine...
      (t,         VRef fc' k' def sp') => do
        debug "expand \{show t} =?= %ref \{k'}"
        case lookup k' !(get) of
          Just (MkEntry name ty (Fn tm)) => unify l t !(vappSpine !(eval [] CBN tm) sp')
          _ => error ctx.fc "unify failed \{show t'} =?= \{show u'} [no Fn]\n  env is \{show ctx.env} \{show $ map fst ctx.types}"
      -- REVIEW I'd like to quote this back, but we have l that aren't in the environment.
      _ => error ctx.fc "unify failed \{show t'} =?= \{show u'} \n  env is \{show ctx.env} \{show $ map fst ctx.types}"
    where
      lookupVar : Nat -> Maybe Val
      lookupVar k = let l = length ctx.env in
        if k > l
          then Nothing
          else case getAt ((l `minus` k) `minus` 1) ctx.env of
            Just (VVar{}) => Nothing
            Just v => Just v
            Nothing => Nothing


unifyCatch : FC -> Context -> Val -> Val -> M ()
unifyCatch fc ctx ty' ty = do
    res <- catchError (unify ctx ctx.lvl ty' ty) $ \(E x str) => do
      let names = toList $ map fst ctx.types
      debug "fail \{show ty'} \{show ty}"
      a <- quote ctx.lvl ty'
      b <- quote ctx.lvl ty
      let msg = "\n  failed to unify \{pprint names a}\n    with \{pprint names b}\n  " <+> str
      throwError (E fc msg)
    case res of
      MkResult [] => pure ()
      cs => error fc "Unification yields constraints \{show cs.constraints}"

insert : (ctx : Context) -> Tm -> Val -> M (Tm, Val)
insert ctx tm ty = do
  case !(forceMeta ty) of
    VPi fc x Implicit a b => do
      m <- freshMeta ctx fc
      mv <- eval ctx.env CBN m
      insert ctx (App emptyFC tm m) !(b $$ mv)
    va => pure (tm, va)

-- lookupName : Context -> Raw -> M (Maybe (Tm, Val))
-- lookupName ctx (RVar fc nm) = go 0 ctx.types
--   where
--     go : Nat -> Vect n (String, Val)  -> M  (Maybe (Tm, Val))
--     go i [] = case lookup nm !(get) of
--       Just (MkEntry name ty def) => pure $ Just (Ref fc nm def, !(eval [] CBN ty))
--       Nothing => pure Nothing
--     go i ((x, ty) :: xs) = if x == nm then pure $ Just (Bnd fc i, ty)
--       else go (i + 1) xs
-- lookupName ctx _ = pure Nothing


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

public export
record Problem where
  constructor MkProb
  clauses : List Clause
  -- I think a pi-type representing the pattern args -> goal, so we're checking
  -- We might pull out the pattern abstraction to a separate step and drop pats from clauses.
  ty : Val

-- Might have to move this if Check reaches back in...

fresh : {auto ctx : Context} -> String -> String
fresh base = base ++ "$" ++ show (length ctx.env)

-- The result is a casetree, but it's in Tm
export
buildTree : Context -> Problem -> M Tm

introClause : String -> Icit -> Clause -> M Clause
-- I don't think this makes a difference?
introClause nm Implicit (MkClause fc cons pats expr) = pure $ MkClause fc ((nm, PatWild fc) :: cons) pats expr
introClause nm icit (MkClause fc cons [] expr) = error fc "Clause size doesn't match"
introClause nm icit (MkClause fc cons (pat :: pats) expr) = pure $ MkClause fc ((nm, pat) :: cons) pats expr

-- A split candidate looks like x /? Con ...
-- we need a type here. I pulled if off of the
-- pi-type, but do we need metas solved or dependents split?
-- this may dot into a dependent.
findSplit : List Constraint -> Maybe Constraint
findSplit [] = Nothing
    -- FIXME look up type, ensure it's a constructor
findSplit (x@(nm, PatCon _ cnm pats) :: xs) = Just x
findSplit (_ :: xs) = findSplit xs


-- ***************
-- right, I think we rewrite the names in the context before running raw and we're good to go?
-- We have stuff like S k /? x, but I think we can back up to whatever the scrutinee variable was?

-- we could pass into build case and use it for   (x /? y)

-- TODO, we may need to filter these for the situation.
getConstructors : Context -> Val -> M (List (String, Nat, Tm))
getConstructors ctx (VRef fc nm _ _) = do
  names <- lookupTCon nm
  traverse lookupDCon names
  where
    lookupTCon : String -> M (List String)
    lookupTCon str = case lookup nm !get of
        (Just (MkEntry name type (TCon names))) => pure names
        _ => error fc "Not a type constructor \{nm}"
    lookupDCon : String -> M (String, Nat, Tm)
    lookupDCon nm = do
      case lookup nm !get of
        (Just (MkEntry name type (DCon k str))) => pure (name, k, type)
        Just _ => error fc "Internal Error: \{nm} is not a DCon"
        Nothing => error fc "Internal Error: DCon \{nm} not found"
getConstructors ctx tm = error (getValFC tm) "Not a type constructor \{show tm}"

-- Extend environment with fresh variables from a pi-type
-- return context, remaining type, and list of names
extendPi : Context -> Val -> SnocList Bind -> M (Context, Val, List Bind)
extendPi ctx (VPi x str icit a b) nms = do
    let nm = fresh "pat"
    let ctx' = extend ctx nm a
    let v = VVar emptyFC (length ctx.env) [<]
    tyb <- b $$ v
    extendPi ctx' tyb (nms :< MkBind nm icit a)
extendPi ctx ty nms = pure (ctx, ty, nms <>> [])

-- filter clause

-- FIXME - I don't think we're properly noticing

updateContext : Context -> List (Nat, Val) -> M Context
updateContext ctx [] = pure ctx
updateContext ctx ((k, val) :: cs) = let ix = (length ctx.env `minus` k) `minus` 1 in
  pure $ {env $= makeLet ix} ctx
  where
    makeLet : Nat -> Env -> Env
    makeLet _ [] = ?nothing_to_update
    makeLet 0 ((VVar fc j [<]) :: xs) = val :: xs
    makeLet 0 (_ :: xs) = ?not_a_var
    makeLet (S k) (x :: xs) = x :: makeLet k xs

-- ok, so this is a single constructor, CaseAlt
-- since we've gotten here, we assume it's possible and we better have at least
-- one valid clause
buildCase : Context -> Problem -> String -> Val -> (String, Nat, Tm) -> M CaseAlt
buildCase ctx prob scnm scty (dcName, _, ty) = do
  debug "CASE \{scnm} \{dcName} \{pprint (names ctx) ty}"
  vty <- eval [] CBN ty
  (ctx', ty', vars) <- extendPi ctx (vty) [<]

  -- what is the goal?
  -- we have something here that informs what happens in the casealt, possibly tweaking
  -- context or goal
  -- e.g. we get to end of Just {a} x  and goal is Maybe Val, we want `let a = Val` in context.
  -- likewise if the constructor says `Foo String` and goal is `Foo x` we know x is String in this branch.

  -- we need unify to hand constraints back...
  -- we may need to walk through the case alt constraint and discharge or drop things?

  -- should I somehow make those holes? It would be nice to not make the user dot it.
  -- And we don't _need_ a solution, just if it's unified against

  -- I think I'm going down a different road than Idris..


  -- do this or see how other people manage?
  -- this puts the failure on the LHS
  -- unifying these should say say VVar 1 is Nat.
  -- ERROR at (23, 0): unify failed (%var 1 [< ]) =?= (%ref Nat [< ]) [no Fn]
  res <- unify ctx' (length ctx.env) ty' scty
  debug "scty \{show scty}"
  debug "UNIFY results \{show res.constraints}"
  debug "before types: \{show ctx'.types}"
  debug "before env: \{show ctx'.env}"

  -- So we go and stuff stuff into the environment, which I guess gets it into the RHS,
  -- but doesn't touch goal...
  ctx' <- updateContext ctx' res.constraints
  debug "context types: \{show ctx'.types}"
  debug "context env: \{show ctx'.env}"
  -- This doesn't really update existing val... including types in the context.

  -- What if all of the pattern vars are defined to meta

  debug "(dcon \{show dcName} ty \{show ty'} scty \{show scty}"
  debug "(dcon \{show dcName}) (vars \{show vars}) clauses were"
  for_ prob.clauses $ (\x => debug "    \{show x}")
  let clauses = mapMaybe (rewriteClause vars) prob.clauses
  debug "and now:"
  for_ clauses $ (\x => debug "    \{show x}")
  -- So ideally we'd know which position we're splitting and the surrounding context
  -- That might be a lot to carry forward (maybe a continuation?) but we could carry
  -- backwards as a List Missing that we augment as we go up.
  -- We could even stick a little "throw error" tree in here for the case.
  -- even going backward, we don't really know where pat$n falls into the expression.
  -- It would need to keep track of its position. Then fill in the slots (wild vs PCons), or
  -- wrapping with PCons as we move back up.  E.g. _ (Cons _ (Cons _ _)) _ _ could be missing
  when (length clauses == 0) $ error ctx.fc "Missing case for \{dcName} splitting \{scnm}"
  tm <- buildTree ctx' (MkProb clauses prob.ty)
  pure $ CaseCons dcName (map getName vars) tm
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


    -- we'll want implicit patterns at some point, for now we wildcard implicits because
    -- we don't have them
    makeConst : List Bind -> List Pattern -> List (String, Pattern)
    makeConst [] [] = []
    -- need M in here to throw.
    makeConst [] (pat :: pats) = ?extra_patterns
    --
    makeConst ((MkBind nm Implicit x) :: xs) [] = (nm, PatWild emptyFC) :: makeConst xs []
    makeConst ((MkBind nm Explicit x) :: xs) [] = ?extra_binders_2
    makeConst ((MkBind nm Implicit x) :: xs) (pat :: pats) = (nm, PatWild (getFC pat)) :: makeConst xs (pat :: pats)
    makeConst ((MkBind nm Explicit x) :: xs) (pat :: pats) = (nm, pat) :: makeConst xs pats

    rewriteCons : List Bind -> List Constraint -> List Constraint -> Maybe (List Constraint)
    rewriteCons vars [] acc = Just acc
    rewriteCons vars (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          PatVar _ s => Just $ c :: (xs ++ acc)
          PatWild _ => Just $ c :: (xs ++ acc)
          PatCon _ str ys => if str == dcName
            then Just $ (makeConst vars ys) ++ xs ++ acc
            else Nothing
        else rewriteCons vars xs (c :: acc)

    rewriteClause : List Bind -> Clause -> Maybe Clause
    rewriteClause vars (MkClause fc cons pats expr) = pure $ MkClause fc !(rewriteCons vars cons []) pats expr



lookupName : Context -> String  -> Maybe (Tm, Val)
lookupName ctx name = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val) -> Maybe (Tm, Val)
    go ix [] = Nothing
    -- FIXME - we should stuff a Binder of some sort into "types"
    go ix ((nm, ty) :: xs) = if nm == name then Just (Bnd emptyFC ix, ty) else go (S ix) xs

-- FIXME need to check done here...
      -- If all of the constraints are assignments, fixup context and type check
      -- else bail:

      -- error fc "Stuck, no splits \{show constraints}"

checkDone : Context -> List (String, Pattern) -> Raw -> Val -> M Tm
checkDone ctx [] body ty = do
  debug "DONE-> check body \{show body} at \{show ty}"
  debug "\{show ctx.env}"
  debug "\{show ctx.types}"
  got <- check ctx body ty
  debug "DONE<- got \{pprint (names ctx) got}"
  pure got
checkDone ctx ((x, PatWild _) :: xs) body ty = checkDone ctx xs body ty
checkDone ctx ((nm, (PatVar _ nm')) :: xs) body ty = checkDone ({ types $= rename } ctx) xs body ty
  where
    rename : Vect n (String, Val) -> Vect n (String, Val)
    rename [] = []
    rename ((name, ty) :: xs) =
      if name == nm
        then (nm', ty) :: xs
        else (name, ty) :: rename xs

checkDone ctx ((x, pat) :: xs) body ty = error emptyFC "stray constraint \{x} /? \{show pat}"

-- This process is similar to extendPi, but we need to stop
-- if one clause is short on patterns.
buildTree ctx (MkProb [] ty) = error emptyFC "no clauses"
buildTree ctx prob@(MkProb ((MkClause fc cons (x :: xs) expr) :: cs) (VPi _ str icit a b)) = do
  let l = length ctx.env
  let nm = fresh "pat"
  let ctx' = extend ctx nm a
  -- type of the rest
  clauses <- traverse (introClause nm icit) prob.clauses
  -- REVIEW fc from a pat?
  vb <- b $$ VVar fc l [<]
  Lam fc nm <$> buildTree ctx' ({ clauses := clauses, ty := vb } prob)
buildTree ctx prob@(MkProb ((MkClause fc cons pats@(x :: xs) expr) :: cs) ty) =
  error fc "Extra pattern variables \{show pats}"
buildTree ctx prob@(MkProb ((MkClause fc [] [] expr) :: cs) ty) = check (withPos ctx fc) expr ty
-- need to find some name we can split in (x :: xs)
-- so LHS of constraint is name (or VVar - if we do Val)
-- then run the split
buildTree ctx prob@(MkProb ((MkClause fc constraints [] expr) :: cs) ty) = do
  debug "buildTree \{show constraints} \{show expr}"
  let Just (scnm, pat) := findSplit constraints
    | _ => checkDone ctx constraints expr ty

  debug "SPLIT on \{scnm} because \{show pat}"
  let Just (sctm, scty) := lookupName ctx scnm
    | _ => error fc "Internal Error: can't find \{scnm} in environment"

  cons <- getConstructors ctx scty
  alts <- traverse (buildCase ctx prob scnm scty) cons

  pure $ Case fc sctm alts


check ctx tm ty = case (tm, !(forceType ty)) of
  (RCase fc rsc alts, ty) => do
    -- We've got a beta redex or need to do something...
    -- Maybe we can let the scrutinee and jump into the middle?
    (sc, scty) <- infer ctx rsc

    let scnm = fresh "sc"
    -- FIXME FC
    let clauses = map (\(MkAlt pat rawRHS) =>MkClause fc [(scnm, pat)] [] rawRHS ) alts
    let ctx' = extend ctx scnm scty
    cons <- getConstructors ctx' scty
    alts <- traverse (buildCase ctx' (MkProb clauses ty) scnm scty) cons

    pure $ Case fc sc alts

    -- buildTree ctx (MkProb{})
    -- ?hole
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
      unifyCatch fc ctx tty (VPi fc ":ins" icit a b)
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

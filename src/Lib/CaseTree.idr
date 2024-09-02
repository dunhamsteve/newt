||| Builds a case tree from clauses.
||| Follow §5.2 in Jesper Cockx paper Elaborating Dependent (co)pattern matching
module Lib.CaseTree

import Data.IORef
import Data.String
import Data.Vect
import Data.List
import Debug.Trace
import Lib.Types
import Lib.TopContext
-- Will be a circular reference if we have case in terms
import Lib.Check
import Lib.TT
import Lib.Syntax


-- ok, so new idea:

-- we make a meta for each patvar
-- then "solve" the meta when we match stuff up.
-- a meta is something we can change

-- but the solutions vary per branch. n is S k in one branch and Z in another.
-- and metas are essentially global.

-- NEXT So on LHS, I think we need to collect constraints pat$0 = Val and change
-- the entry in the environment to a let?

-- Except I think the let might reference something not bound yet? For RHS (a raw), we
-- can shadow. For expected type, we might have to mess with the Val?

-- On RHS I don't think unification can assign a value to a name.

-- exempli gratia
-- fromMaybe : Maybe Nat -> Nat
-- fromMaybe (Just x) = x
--                      ^- currently
-- fromMaybe Nothing = Z


-- LHSProblem
-- List of [ E ] qbar --> rhs
-- E is bag of constraints:
--      { w_k /? p_k : A_k | k = 1 ... l }
--      qbar copatterns


-- Case Tree is Σ;Γ ⊢ P | f qbar := Q : C ⤳ Σ'
-- rules fig 10 refined version of fig 7, so well type.
-- I guess fig 7 will tell us how to typecheck results if we want to skip
-- to casetree or verify

-- Agda or Lean would look more like the paper here...

-- I may need defs/lets in the environment

-- Simplified guess at type
-- We'll want to add dotted values and push this out
-- where the parser can see it

-- I've got a janky typescript POC without types.

-- add FC to Pattern for errors?

-- on the left we have either a bound variable or a constructor applied to bound variables
-- on the right we have a pattern
-- Raw will refer to variables in pattern, so we either need to subst into Raw, which sounds painful
-- or get the variables into scope in a way that the Raw can use them
-- The pvars point to bound variables _or_ full expressions (Val) of a dcon applied to bound vars
-- (e.g. S k). Perhaps something like `let` or a specific `pvar` binder?

-- when we INTRO, we pop a pat from pats and a type from ty
-- add to gamma
-- add a constraint to each clause binding the var t to the pat
-- wrap the result of buildTree with a lambda

-- intro all the things
-- split all the things
-- turn matches into subst
-- see if we're good (no pats, no constraints)

-- a case statement doesn't have pats, intro has been done
-- already, and we have a pile of clauses referencing a
-- name in the context.

-- a function def can let intro happen, so we could have
-- different lengths of args.

-- We're pulling type from the context, but we'll have it here if we use
-- Bind more widely
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

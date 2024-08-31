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

introClause : String -> Clause -> M Clause
introClause nm (MkClause fc cons [] expr) = error fc "Clause size doesn't match"
introClause nm (MkClause fc cons (pat :: pats) expr) = pure $ MkClause fc ((nm, pat) :: cons) pats expr

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
getConstructors ctx (VRef fc nm _ sc) = do
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
-- NEXT This doesn't work, unsound.
-- We need all of these vars with icity _and_ to insert implicits in the pattern
-- extendPi ctx (VPi x str Implicit a b) nms = do
--     let nm = fresh "pat"
--     let ctx' = extend ctx nm a
--     let v = VVar emptyFC (length ctx.env) [<]
--     tyb <- b $$ v
--     extendPi ctx' tyb nms
extendPi ctx (VPi x str icit a b) nms = do
    let nm = fresh "pat"
    let ctx' = extend ctx nm a
    let v = VVar emptyFC (length ctx.env) [<]
    tyb <- b $$ v
    extendPi ctx' tyb (nms :< MkBind nm icit a)
extendPi ctx ty nms = pure (ctx, ty, nms <>> [])

-- filter clause

-- FIXME - I don't think we're properly noticing


-- ok, so this is a single constructor, CaseAlt
-- since we've gotten here, we assume it's possible and we better have at least
-- one valid clause
buildCase : Context -> Problem -> String -> (String, Nat, Tm) -> M CaseAlt
buildCase ctx prob scnm (dcName, _, ty) = do
  vty <- eval [] CBN ty
  (ctx', ty', vars) <- extendPi ctx (vty) [<]

  debug "clauses were \{show prob.clauses} (dcon \{show dcName}) (vars \{show vars})"
  let clauses = mapMaybe (rewriteClause vars) prob.clauses
  debug "    and now \{show clauses}"
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
            then Just $ (makeConst vars ys) ++ acc
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
checkDone ctx [] body ty = check ctx body ty
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
buildTree ctx prob@(MkProb ((MkClause fc cons (x :: xs) expr) :: cs) (VPi _ str Implicit a b)) = do
  let l = length ctx.env
  let nm = fresh "pat"
  let ctx' = extend ctx nm a
  -- type of the rest
  -- clauses <- traverse (introClause nm) prob.clauses
  vb <- b $$ VVar fc l [<]
  Lam fc nm <$> buildTree ctx' ({ ty := vb } prob)
buildTree ctx prob@(MkProb ((MkClause fc cons (x :: xs) expr) :: cs) (VPi _ str icit a b)) = do
  let l = length ctx.env
  let nm = fresh "pat"
  let ctx' = extend ctx nm a
  -- type of the rest
  clauses <- traverse (introClause nm) prob.clauses
  -- REVIEW fc from a pat?
  vb <- b $$ VVar fc l [<]
  Lam fc nm <$> buildTree ctx' ({ clauses := clauses, ty := vb } prob)
buildTree ctx prob@(MkProb ((MkClause fc cons pats@(x :: xs) expr) :: cs) ty) =
  error fc "Extra pattern variables \{show pats}"
buildTree ctx prob@(MkProb ((MkClause fc [] [] expr) :: cs) ty) = check ctx expr ty
-- need to find some name we can split in (x :: xs)
-- so LHS of constraint is name (or VVar - if we do Val)
-- then run the split
buildTree ctx prob@(MkProb ((MkClause fc constraints [] expr) :: cs) ty) = do
  debug "buildTree \{show constraints} \{show expr}"
  let Just (scnm, pat) := findSplit constraints
    | _ => checkDone ctx constraints expr ty

  debug "split on \{scnm} because \{show pat}"
  let Just (sctm, ty') := lookupName ctx scnm
    | _ => error fc "Internal Error: can't find \{scnm} in environment"

  cons <- getConstructors ctx ty'
  alts <- traverse (buildCase ctx prob scnm) cons

  pure $ Case fc sctm alts

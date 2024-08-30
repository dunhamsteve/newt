||| Builds a case tree from clauses.
||| Follow §5.2 in Jesper Cockx paper Elaborating Dependent (co)pattern matching
module Lib.CaseTree

import Data.String
import Data.Vect
import Data.List
import Lib.Types
import Lib.TopContext
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

0 Constraint : Type
Constraint = (String, Pattern)

record Clause where
  constructor MkClause
  fc : FC
  -- I'm including the type of the left, so we can check pats and get the list of possibilities
  -- But maybe rethink what happens on the left.
  -- It's a VVar k or possibly a pattern.
  -- a pattern either is zipped out, dropped (non-match) or is assigned to rhs
  -- if we can do all three then we can have a VVar here.
  cons : List Constraint
  pats : List Pattern
  -- We'll need some context to typecheck this
  -- it has names from Pats, which will need types in the env
  expr : Raw

-- when we INTRO, we pop a pat from pats and a type from ty
-- add to gamma
-- add a constraint to each clause binding the var t to the pat
-- wrap the result of buildTree with a lambda

-- intro all the things
-- split all the things
-- turn matches into subst
-- see if we're good (no pats, no constraints)

-- Do I want Val or Tm here?

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
findSplit (x@(nm, PatCon{}) :: xs) =
    -- FIXME look up type, ensure it's a constructor
    Just x
findSplit (_ :: xs) = findSplit xs


-- ***************
-- right, I think we rewrite the names in the context before running raw and we're good to go?
-- We have stuff like S k /? x, but I think we can back up to whatever the scrutinee variable was?

-- we could pass into build case and use it for   (x /? y)

-- TODO, we may need to filter these for the situation.
getConstructors : Context -> Val -> M (List (String, Nat, Tm))
getConstructors ctx (VRef fc nm (TCon names) sc) = traverse lookupDCon names
  where
    lookupDCon : String -> M (String, Nat, Tm)
    lookupDCon nm = do
      case lookup nm !get of
        (Just (MkEntry name type (DCon k str))) => pure (name, k, type)
        Just _ => error fc "Internal Error: \{nm} is not a DCon"
        Nothing => error fc "Internal Error: DCon \{nm} not found"
getConstructors ctx tm = error (getValFC tm) "Not a type constructor"

-- Extend environment with fresh variables from a pi-type
-- return context, remaining type, and list of names
extendPi : Context -> Val -> SnocList Name -> M (Context, Val, List Name)
extendPi ctx (VPi x str icit a b) nms = do
    let nm = fresh "pat"
    let ctx' = extend ctx nm a
    let v = VVar emptyFC (length ctx.env) [<]
    tyb <- b $$ v
    extendPi ctx' tyb (nms :< nm)
extendPi ctx ty nms = pure (ctx, ty, nms <>> [])

-- filter clause


-- ok, so this is a single constructor, CaseAlt
-- since we've gotten here, we assume it's possible and we better have at least
-- one valid clause
buildCase : Context -> Problem -> String -> (String, Nat, Tm) -> M CaseAlt
buildCase ctx prob scnm (dcName, arity, ty) = do
  vty <- eval [] CBN ty
  (ctx', ty', vars) <- extendPi ctx (vty) [<]
  let clauses = mapMaybe (rewriteClause vars) prob.clauses
  when (length clauses == 0) $ error emptyFC "No valid clauses / missing case / FIXME FC and some details"
  tm <- buildTree ctx' (MkProb clauses ty')
  pure $ CaseCons dcName vars tm
  where
    -- for each clause in prob, find nm on LHS of some constraint, and
    -- "replace" with the constructor and vars.
    --
    -- This will be:
    --   x /? y    can probably just leave this
    --   x /? D a b c  split into three x /? a, y /? b, z /? c
    --   x /? E a b    drop this clause
    -- We get a list of clauses back (a Problem) and then solve that
    -- If they all fail, we have a coverage issue. (Assuming the constructor is valid)


    -- There is a zip here, etc, but are we just re-writing buildTree?
    -- I suppose vars might be the difference?  There may be something to factor out here
    -- essentially we're picking apart Pi, binding variables and constraining them to patterns.
    -- everything we've bound is only used in the PatCon case below.

    rewriteCons : List Name -> List Constraint -> List Constraint -> Maybe (List Constraint)
    rewriteCons vars [] acc = Just acc
    rewriteCons vars (c@(nm, y) :: xs) acc =
      if nm == scnm
        then case y of
          (PatVar s) => Just $ c :: (xs ++ acc)
          PatWild => Just $ c :: (xs ++ acc)
          (PatCon str ys) => if str == dcName
            then Just $ acc ++ (zip vars ys)
            else Nothing
        else rewriteCons vars xs (c :: acc)

    rewriteClause : List Name -> Clause -> Maybe Clause
    rewriteClause vars (MkClause fc cons pats expr) = pure $ MkClause fc !(rewriteCons vars cons []) pats expr



lookupName : Context -> String  -> Maybe (Tm, Val)
lookupName ctx name = go 0 ctx.types
  where
    go : Nat -> Vect n (String, Val) -> Maybe (Tm, Val)
    go ix [] = Nothing
    -- FIXME - we should stuff a Binder of some sort into "types"
    go ix ((nm, ty) :: xs) = if nm == name then Just (Bnd emptyFC ix, ty) else go (S ix) xs

buildTree ctx (MkProb [] ty) = error emptyFC "no clauses"
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
buildTree ctx prob@(MkProb ((MkClause fc xs [] expr) :: cs) ty) = do

  -- REVIEW There is a extendPi here.

  -- We don't need ty here if we're happy with Val...
  let Just (scnm, _) := findSplit xs | _ => error fc "Stuck, no splits"

  let Just (sctm, ty') := lookupName ctx scnm
    | _ => error fc "Internal Error: can't find \{scnm} in environment"

  -- get constructors, for each of them run the problem, build Case result
  cons <- getConstructors ctx ty' -- probably need pi-types too for recursion
  -- we have a case tree for each dcon, from a recursive call, collect into `Case`
  alts <- traverse (buildCase ctx prob scnm) cons

  -- Maybe `scnm` should be something other than a name? Index is not stable,
  -- we're working with term at the moment, so Val isn't great.
  -- But this is elab and we do name -> Bnd in `infer`, so why not.

  pure $ Case fc sctm alts





-- A telescope is a list of binders, right? I've been leaving things as pi types to be explicit


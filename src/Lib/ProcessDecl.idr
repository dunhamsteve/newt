module Lib.ProcessDecl

import Data.IORef
import Data.String
import Data.Vect

import Lib.Elab
import Lib.Parser
import Lib.Syntax
import Lib.TopContext
import Lib.Eval
import Lib.Types
import Lib.Util

-- Check that the arguments are not explicit and the type constructor in codomain matches
-- Later we will build a table of codomain type, and maybe make the user tag the candidates
-- like Idris does with %hint
isCandidate : Val -> Tm -> Bool
isCandidate ty (Pi fc nm Explicit t u) = False
isCandidate ty (Pi fc nm icit t u) = isCandidate ty u
isCandidate (VRef _ nm _ _) (Ref fc nm' def) = nm == nm'
isCandidate ty (App fc t u) = isCandidate ty t
isCandidate _ _ = False


-- This is a crude first pass
-- TODO consider ctx
findMatches : Val -> List TopEntry -> M (List (Tm, MetaContext))
findMatches ty [] = pure []
findMatches ty ((MkEntry name type def@(Fn t)) :: xs) = do
  let True = isCandidate ty type | False => findMatches ty xs
  top <- get
  let ctx = mkCtx top.metas (getFC ty)
  -- FIXME we're restoring state, but the INFO logs have already been emitted
  -- Also redo this whole thing to run during elab, recheck constraints, etc.
  mc <- readIORef top.metas
  catchError {e=Error} (do
      -- TODO sort out the FC here
      let fc = getFC ty
      debug "TRY \{name} : \{pprint [] type} for \{show ty}"
      -- This check is solving metas, so we save mc below in case we want this solution
      tm <- check (mkCtx top.metas fc) (RVar fc name) ty
      debug "Found \{pprint [] tm} for \{show ty}"
      mc' <- readIORef top.metas
      writeIORef top.metas mc
      ((tm, mc') ::) <$> findMatches ty xs)
    (\ err => do
      debug "No match \{show ty} \{pprint [] type} \{showError "" err}"
      writeIORef top.metas mc
      findMatches ty xs)
findMatches ty (y :: xs) = findMatches ty xs

getArity : Tm -> Nat
getArity (Pi x str icit t u) = S (getArity u)
-- Ref or App (of type constructor) are valid
getArity _ = Z

-- Can metas live in context for now?
-- We'll have to be able to add them, which might put gamma in a ref

||| collectDecl collects multiple Def for one function into one
export
collectDecl : List Decl -> List Decl
collectDecl [] = []
collectDecl ((Def fc nm cl) :: rest@(Def _ nm' cl' :: xs)) =
  if nm == nm' then collectDecl (Def fc nm (cl ++ cl') :: xs)
  else (Def fc nm cl :: collectDecl rest)
collectDecl (x :: xs) = x :: collectDecl xs

-- Makes the arg for `solve` when we solve an auto
makeSpine : Nat -> Vect k BD -> SnocList Val
makeSpine k [] = [<]
makeSpine (S k) (Defined :: xs) = makeSpine k xs
makeSpine (S k) (Bound :: xs) = makeSpine k xs :< VVar emptyFC k [<]
makeSpine 0 xs = ?fixme

solveAutos : Nat -> List MetaEntry -> M ()
solveAutos mlen [] = pure ()
solveAutos mlen ((Unsolved fc k ctx ty AutoSolve _) :: es) = do
      debug "AUTO solving \{show k} : \{show ty}"
      -- we want the context here too.
      top <- get
      [(tm,mc)] <- findMatches ty top.defs
        | res => do
          debug "FAILED to solve \{show ty}, matches: \{show $ map (pprint [] . fst) res}"
          solveAutos mlen es
        -- | res => error fc "FAILED to solve \{show ty}, matches: \{show $ map (pprint [] . fst) res}"
      writeIORef top.metas mc
      val <- eval ctx.env CBN tm
      debug "SOLUTION \{pprint [] tm} evaled to \{show val}"
      let sp = makeSpine ctx.lvl ctx.bds
      solve ctx ctx.lvl k sp val
      mc <- readIORef top.metas
      solveAutos mlen (take mlen mc.metas)
solveAutos mlen (_ :: es) = solveAutos mlen es


export
processDecl : Decl -> M ()

-- REVIEW I supposed I could have updated top here instead of the dance with the parser...
processDecl (PMixFix{})  = pure ()

processDecl (TypeSig fc names tm) = do
  top <- get
  for_ names $ \nm => do
    let Nothing := lookup nm top
      | _ => error fc "\{show nm} is already defined"
    pure ()
  putStrLn "-----"
  putStrLn "TypeSig \{unwords names} : \{show tm}"
  ty <- check (mkCtx top.metas fc) tm (VU fc)
  putStrLn "got \{pprint [] ty}"
  -- I was doing this previously, but I don't want to over-expand VRefs
  -- ty' <- nf [] ty
  -- putStrLn "nf \{pprint [] ty'}"
  for_ names $ \nm => modify $ setDef nm ty Axiom

processDecl (PType fc nm ty) = do
  top <- get
  ty' <- check (mkCtx top.metas fc) (maybe (RU fc) id ty) (VU fc)
  modify $ setDef nm ty' PrimTCon

processDecl (PFunc fc nm ty src) = do
  top <- get
  ty <- check (mkCtx top.metas fc) ty (VU fc)
  ty' <- nf [] ty
  putStrLn "pfunc \{nm} : \{pprint [] ty'} := \{show src}"
  modify $ setDef nm ty' (PrimFn src)

processDecl (Def fc nm clauses) = do
  putStrLn "-----"
  putStrLn "def \{show nm}"
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  let Just entry = lookup nm top
    | Nothing => throwError $ E fc "skip def \{nm} without Decl"
  let (MkEntry name ty Axiom) := entry
    | _ => throwError $ E fc "\{nm} already defined"

  putStrLn "check \{nm} ... at \{pprint [] ty}"
  vty <- eval empty CBN ty
  putStrLn "vty is \{show vty}"

  -- I can take LHS apart syntactically or elaborate it with an infer
  clauses' <- traverse (makeClause top) clauses
  tm <- buildTree (mkCtx top.metas fc) (MkProb clauses' vty)
  putStrLn "Ok \{pprint [] tm}"

  mc <- readIORef top.metas
  let mlen = length mc.metas `minus` mstart
  solveAutos mlen (take mlen mc.metas)

  -- Expand metas
  -- tm' <- nf [] tm  -- TODO - nf that expands all metas, Day1.newt is a test case
  tm' <- zonk top 0 [] tm
  putStrLn "NF \{pprint[] tm'}"

  mc <- readIORef top.metas
  for_ (take mlen mc.metas) $ \case
    (Solved fc k soln) => info fc "solve \{show k} as \{pprint [] !(quote 0 soln)}"
    (Unsolved fc k ctx ty User cons) => do
      ty' <- quote ctx.lvl ty
      let names = (toList $ map fst ctx.types)
      -- I want to know which ones are defines. I should skip the `=` bit if they match, I'll need indices in here too.
      env <- for (zip ctx.env (toList ctx.types)) $ \(v, n, ty) => pure "  \{n} : \{pprint names !(quote ctx.lvl ty)} = \{pprint names !(quote ctx.lvl v)}"
      let msg = "\{unlines (toList $ reverse env)}  -----------\n  goal \{pprint names ty'}"
      info fc "User Hole\n\{msg}"
    (Unsolved (l,c) k ctx ty kind cons) => do
      tm <- quote ctx.lvl !(forceMeta ty)
      -- Now that we're collecting errors, maybe we simply check at the end
      -- TODO - log constraints?
      addError $ E (l,c) "Unsolved meta \{show k} \{show kind} type \{pprint (names ctx) tm} \{show $ length cons} constraints"

  debug "Add def \{nm} \{pprint [] tm'} : \{pprint [] ty}"
  modify $ setDef nm ty (Fn tm')

processDecl (DCheck fc tm ty) = do
  top <- get
  putStrLn "check \{show tm} at \{show ty}"
  ty' <- check (mkCtx top.metas fc) tm (VU fc)
  putStrLn "got type \{pprint [] ty'}"
  vty <- eval [] CBN ty'
  res <- check (mkCtx top.metas fc) ty vty
  putStrLn "got \{pprint [] res}"
  norm <- nf [] res
  putStrLn "norm \{pprint [] norm}"
  putStrLn "NF "

processDecl (Data fc nm ty cons) = do
  top <- get
  tyty <- check (mkCtx top.metas fc) ty (VU fc)
  modify $ setDef nm tyty Axiom
  cnames <- for cons $ \x => case x of
      (TypeSig fc names tm) => do
          dty <- check (mkCtx top.metas fc) tm (VU fc)
          debug "dty \{show names} is \{pprint [] dty}"

          -- We only check that codomain uses the right type constructor
          -- We know it's in U because it's part of a checked Pi type
          let (codomain, tele) = splitTele dty
          -- for printing
          let tnames = reverse $ map (\(MkBind _ nm _ _) => nm) tele
          let (Ref _ hn _, args) := funArgs codomain
            | (tm, _) => error (getFC tm) "expected \{nm} got \{pprint tnames tm}"
          when (hn /= nm) $
            error (getFC codomain) "Constructor codomain is \{pprint tnames codomain} rather than \{nm}"

          for_ names $ \ nm' => modify $ setDef nm' dty (DCon (getArity dty) nm)
          pure names
      _ => throwError $ E (0,0) "expected constructor declaration"
  putStrLn "setDef \{nm}  TCon \{show $ join cnames}"
  modify $ setDef nm tyty (TCon (join cnames))
  pure ()
  where
    checkDeclType : Tm -> M ()
    checkDeclType (U _) = pure ()
    checkDeclType (Pi _ str icit t u) = checkDeclType u
    checkDeclType _ = error fc "data type doesn't return U"

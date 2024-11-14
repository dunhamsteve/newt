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
findMatches : Context -> Val -> List TopEntry -> M (List (Tm, MetaContext))
findMatches ctx ty [] = pure []
findMatches ctx ty ((MkEntry name type def@(Fn t)) :: xs) = do
  let True = isCandidate ty type | False => findMatches ctx ty xs
  top <- get
  -- let ctx = mkCtx top.metas (getFC ty)
  -- FIXME we're restoring state, but the INFO logs have already been emitted
  -- Also redo this whole thing to run during elab, recheck constraints, etc.
  mc <- readIORef top.metas
  catchError {e=Error} (do
      -- TODO sort out the FC here
      let fc = getFC ty
      debug "TRY \{name} : \{pprint [] type} for \{show ty}"
      -- This check is solving metas, so we save mc below in case we want this solution
      -- tm <- check (mkCtx top.metas fc) (RVar fc name) ty
      tm <- check ctx (RVar fc name) ty
      debug "Found \{pprint [] tm} for \{show ty}"
      mc' <- readIORef top.metas
      writeIORef top.metas mc
      ((tm, mc') ::) <$> findMatches ctx ty xs)
    (\ err => do
      debug "No match \{show ty} \{pprint [] type} \{showError "" err}"
      writeIORef top.metas mc
      findMatches ctx ty xs)
findMatches ctx ty (y :: xs) = findMatches ctx ty xs

contextMatches : Context -> Val -> M (List (Tm, MetaContext))
contextMatches ctx ty = go (zip ctx.env (toList ctx.types))
  where
    go : List (Val, String, Val) -> M (List (Tm, MetaContext))
    go [] = pure []
    go ((tm, nm, vty) :: xs) = do
      type <- quote ctx.lvl vty
      let True = isCandidate ty type | False => go xs
      top <- get
      mc <- readIORef top.metas
      catchError {e=Error} (do
          debug "TRY context \{nm} : \{pprint (names ctx) type} for \{show ty}"
          unifyCatch (getFC ty) ctx ty vty
          mc' <- readIORef top.metas
          writeIORef top.metas mc
          tm <- quote ctx.lvl tm
          ((tm, mc') ::) <$> go xs)
        (\ err => do
          debug "No match \{show ty} \{pprint (names ctx) type} \{showError "" err}"
          writeIORef top.metas mc
          go xs)

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
      [(tm, mc)] <- case !(contextMatches ctx ty) of
            [] => findMatches ctx ty top.defs
            xs => pure xs
        | res => do
          debug "FAILED to solve \{show ty}, matches: \{show $ map (pprint [] . fst) res}"
          solveAutos mlen es
        -- | res => error fc "FAILED to solve \{show ty}, matches: \{show $ map (pprint [] . fst) res}"
      writeIORef top.metas mc
      val <- eval ctx.env CBN tm
      debug "SOLUTION \{pprint [] tm} evaled to \{show val}"
      let sp = makeSpine ctx.lvl ctx.bds
      solve ctx.env k sp val
      mc <- readIORef top.metas
      solveAutos mlen (take mlen mc.metas)
solveAutos mlen (_ :: es) = solveAutos mlen es

dumpEnv : Context -> M String
dumpEnv ctx =
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

logMetas : Nat -> M ()
logMetas mstart = do
  -- FIXME, now this isn't logged for Sig / Data.
  top <- get
  mc <- readIORef top.metas
  let mlen = length mc.metas `minus` mstart
  for_ (reverse $ take mlen mc.metas) $ \case
    (Solved fc k soln) => info fc "solve \{show k} as \{pprint [] !(quote 0 soln)}"
    (Unsolved fc k ctx ty User cons) => do
      ty' <- quote ctx.lvl ty
      let names = (toList $ map fst ctx.types)
      env <- dumpEnv ctx
      let msg = "\{env}  -----------\n  \{pprint names ty'}"
      info fc "User Hole\n\{msg}"
    (Unsolved (l,c) k ctx ty kind cons) => do
      tm <- quote ctx.lvl !(forceMeta ty)
      -- Now that we're collecting errors, maybe we simply check at the end
      -- TODO - log constraints?
      -- FIXME in Combinatory, the val doesn't match environment?
      let msg = "Unsolved meta \{show k} \{show kind} type \{pprint (names ctx) tm} \{show $ length cons} constraints"
      msgs <- for cons $ \ (MkMc fc env sp val) => do
            putStrLn "  ENV \{show env}"
            pure "  (m\{show k} (\{unwords $ map show $ sp <>> []}) =?= \{show val}"
      addError $ E (l,c) $ unlines ([msg] ++ msgs)

export
processDecl : Decl -> M ()

-- REVIEW I supposed I could have updated top here instead of the dance with the parser...
processDecl (PMixFix{})  = pure ()

processDecl (TypeSig fc names tm) = do
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  for_ names $ \nm => do
    let Nothing := lookup nm top
      | _ => error fc "\{show nm} is already defined"
    pure ()
  putStrLn "-----"
  putStrLn "TypeSig \{unwords names} : \{show tm}"
  ty <- check (mkCtx top.metas fc) tm (VU fc)
  debug "got \{pprint [] ty}"
  for_ names $ \nm => setDef nm fc ty Axiom
  -- Zoo4eg has metas in TypeSig, need to decide if I want to support that going forward.
  -- logMetas mstart

processDecl (PType fc nm ty) = do
  top <- get
  ty' <- check (mkCtx top.metas fc) (maybe (RU fc) id ty) (VU fc)
  setDef nm fc ty' PrimTCon

processDecl (PFunc fc nm ty src) = do
  top <- get
  ty <- check (mkCtx top.metas fc) ty (VU fc)
  ty' <- nf [] ty
  putStrLn "pfunc \{nm} : \{pprint [] ty'} := \{show src}"
  setDef nm fc ty' (PrimFn src)

processDecl (Def fc nm clauses) = do
  putStrLn "-----"
  putStrLn "def \{show nm}"
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  let Just entry = lookup nm top
    | Nothing => throwError $ E fc "No declaration for \{nm}"
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
  -- tm' <- nf [] tm  -- TODO - make nf that expands all metas, Day1.newt is a test case
  tm' <- zonk top 0 [] tm
  putStrLn "NF \{pprint[] tm'}"
  debug "Add def \{nm} \{pprint [] tm'} : \{pprint [] ty}"
  updateDef nm fc ty (Fn tm')
  logMetas mstart

processDecl (DCheck fc tm ty) = do
  putStrLn "----- DCheck"
  top <- get

  putStrLn "INFO at \{show fc}: check \{show tm} at \{show ty}"
  ty' <- check (mkCtx top.metas fc) ty (VU fc)
  putStrLn "  got type \{pprint [] ty'}"
  vty <- eval [] CBN ty'
  res <- check (mkCtx top.metas fc) tm vty
  putStrLn "  got \{pprint [] res}"
  norm <- nf [] res
  putStrLn "  NF \{pprint [] norm}"
  norm <- nfv [] res
  putStrLn "  NFV \{pprint [] norm}"

processDecl (Data fc nm ty cons) = do
  putStrLn "-----"
  putStrLn "process data \{nm}"
  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  tyty <- check (mkCtx top.metas fc) ty (VU fc)
  case lookup nm top of
    Just (MkEntry name type Axiom) => do
      unifyCatch fc (mkCtx top.metas fc) !(eval [] CBN tyty) !(eval [] CBN type)
    Just (MkEntry name type _) => error fc "\{show nm} already declared"
    Nothing => setDef nm fc tyty Axiom
  cnames <- for cons $ \x => case x of
      (TypeSig fc names tm) => do
          debug "check dcon \{show names} \{show tm}"
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

          for_ names $ \ nm' => do
            setDef nm' fc dty (DCon (getArity dty) nm)
          pure names
      _ => throwError $ E (0,0) "expected constructor declaration"
  putStrLn "setDef \{nm}  TCon \{show $ join cnames}"
  updateDef nm fc tyty (TCon (join cnames))
  logMetas mstart
  where
    checkDeclType : Tm -> M ()
    checkDeclType (U _) = pure ()
    checkDeclType (Pi _ str icit t u) = checkDeclType u
    checkDeclType _ = error fc "data type doesn't return U"

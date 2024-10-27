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


-- This is a crude first pass
-- TODO consider ctx
findMatches : Val -> List TopEntry -> M (List Tm)
findMatches ty [] = pure []
findMatches ty ((MkEntry name type def@(Fn t)) :: xs) = do
  top <- get
  let ctx = mkCtx top.metas (getFC ty)
  -- FIXME we're restoring state, but the INFO logs have already been emitted
  -- Also redo this whole thing to run during elab, recheck constraints, etc.
  mc <- readIORef top.metas
  catchError {e=Error} (do
      -- TODO sort out the FC here
      let fc = getFC ty
      tm <- check (mkCtx  top.metas fc) (RVar fc name) ty
      debug "Found \{pprint [] tm} for \{show ty}"
      (tm ::) <$> findMatches ty xs)
    (\ _ => do
      writeIORef top.metas mc
      debug "No match \{show ty} \{pprint [] type}"
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
  for_ (take mlen mc.metas) $ \case
    (Unsolved fc k ctx ty AutoSolve) => do
      debug "auto solving \{show k} : \{show ty}"
      -- we want the context here too.
      [tm] <- findMatches ty top.defs
        | res => error fc "Failed to solve \{show ty}, matches: \{show $ map (pprint []) res}"
      val <- eval ctx.env CBN tm
      let sp = makeSpine ctx.lvl ctx.bds
      solve ctx ctx.lvl k sp val
      pure ()
    _ => pure ()

  tm' <- zonk top 0 [] tm
  putStrLn "NF \{pprint[] tm'}"

  mc <- readIORef top.metas
  -- for_ (take mlen mc.metas) $ \case
  for_ (mc.metas) $ \case
    (Solved k x) => pure ()
    (Unsolved (l,c) k ctx ty User) => do
      -- TODO print here instead of during Elab
      pure ()
    (Unsolved (l,c) k ctx ty kind) => do
      tm <- quote ctx.lvl !(forceMeta ty)
      -- Now that we're collecting errors, maybe we simply check at the end
      addError $ E (l,c) "Unsolved meta \{show k} \{show kind} type \{pprint (names ctx) tm}"
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

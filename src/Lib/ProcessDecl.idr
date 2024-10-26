module Lib.ProcessDecl

import Data.IORef
import Data.String

import Lib.Elab
import Lib.Parser
import Lib.Syntax
import Lib.TopContext
import Lib.Eval
import Lib.Types
import Lib.Util

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
  tm' <- zonk top 0 [] tm
  putStrLn "NF \{pprint[] tm'}"
  mc <- readIORef top.metas

  -- Maybe here we try search?

  for_ (drop mstart mc.metas) $ \case
    (Solved k x) => pure ()
    (Unsolved (l,c) k ctx ty User) => do
      -- TODO print here
      pure ()
    (Unsolved (l,c) k ctx ty kind) => do
      tm <- quote ctx.lvl !(forceMeta ty)
      -- Now that we're collecting errors, maybe we simply check at the end
      addError $ E (l,c) "Unsolved meta \{show k} type \{pprint (names ctx) tm}"
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

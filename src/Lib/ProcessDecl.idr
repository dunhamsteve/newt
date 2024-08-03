module Lib.ProcessDecl

import Data.IORef

import Lib.Types
import Lib.Parser
import Lib.TT
import Lib.TopContext
import Lib.Check
import Lib.Syntax

export
processDecl : Decl -> M ()
processDecl (TypeSig nm tm) = do
  top <- get
  putStrLn "-----"
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check (mkCtx top.metas) tm VU
  ty' <- nf [] ty
  putStrLn "got \{pprint [] ty'}"
  modify $ claim nm ty'

processDecl (Def nm raw) = do
  putStrLn "-----"
  putStrLn "def \{show nm}"
  ctx <- get
  let pos = case raw of
        RSrcPos pos _ => pos
        _ => (0,0)

  let Just entry = lookup nm ctx
    | Nothing => throwError $ E pos "skip def \{nm} without Decl"
  let (MkEntry name ty Axiom) := entry
    | _ => throwError $ E pos "\{nm} already defined"
  putStrLn "check \{nm} = \{show raw} at \{pprint [] ty}"
  vty <- eval empty CBN ty
  putStrLn "vty is \{show vty}"
  tm <- check (mkCtx ctx.metas) raw vty
  putStrLn "Ok \{pprint [] tm}"

  mc <- readIORef ctx.metas
  for_ mc.metas $ \case
    (Solved k x) => pure ()
    (Unsolved (l,c) k xs) => do
      -- should just print, but it's too subtle in the sea of messages
      -- putStrLn "ERROR at (\{show l}, \{show c}): Unsolved meta \{show k}"
      throwError $ E (l,c) "Unsolved meta \{show k}"

  put (addDef ctx nm tm ty)

processDecl (DCheck tm ty) = do

  top <- get
  putStrLn "check \{show tm} at \{show ty}"
  ty' <- check (mkCtx top.metas) tm VU
  putStrLn "got type \{pprint [] ty'}"
  vty <- eval [] CBN ty'
  res <- check (mkCtx top.metas) ty vty
  putStrLn "got \{pprint [] res}"
  norm <- nf [] res
  putStrLn "norm \{pprint [] norm}"
  -- top <- get
  -- ctx <- mkCtx top.metas
  -- I need a type to check against
  -- norm <- nf [] x
  putStrLn "NF "

processDecl (DImport str) = throwError $ E (0,0) "import not implemented"

processDecl (Data nm ty cons) = do
  -- It seems like the FC for the errors are not here?
  ctx <- get
  tyty <- check (mkCtx ctx.metas) ty VU
  -- FIXME we need this in scope, but need to update
  modify $ claim nm tyty
  ctx <- get
  cnames <- for cons $ \x => case x of
      -- expecting tm to be a Pi type
      (TypeSig nm' tm) => do
          ctx <- get
          -- TODO check pi type ending in full tyty application
          -- TODO count arity
          dty <- check (mkCtx ctx.metas) tm VU
          modify $ defcon nm' 0 nm dty
          pure nm'
      _ => throwError $ E (0,0) "expected constructor declaration"
  -- TODO check tm is VU or Pi ending in VU
  -- Maybe a pi -> binders function
  -- TODO we're putting in axioms, we need constructors
  -- for each constructor, check and add
  modify $ deftype nm tyty cnames
  pure ()
  where
    checkDeclType : Tm -> M ()
    checkDeclType U = pure ()
    checkDeclType (Pi str icit t u) = checkDeclType u
    checkDeclType _ = throwError $ E (0,0) "data type doesn't return U"



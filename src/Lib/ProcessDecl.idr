module Lib.ProcessDecl

import Data.IORef

import Lib.CaseTree
import Lib.Check
import Lib.Parser
import Lib.Syntax
import Lib.TopContext
import Lib.TT
import Lib.Types
import Lib.Util

getArity : Tm -> Nat
getArity (Pi x str icit t u) = S (getArity u)
-- Ref or App (of type constructor) are valid
getArity _ = Z

-- Can metas live in context for now?
-- We'll have to be able to add them, which might put gamma in a ref

-- collect Defs into List Decl, special type, or add Defs to Decl?

export
collectDecl : List Decl -> List Decl
collectDecl [] = []
collectDecl ((Def fc nm cl) :: rest@(Def _ nm' cl' :: xs)) =
  if nm == nm' then collectDecl (Def fc nm (cl ++ cl') :: xs)
  else (Def fc nm cl :: collectDecl rest)
collectDecl (x :: xs) = x :: collectDecl xs

export
processDecl : Decl -> M ()
processDecl (TypeSig fc nm tm) = do
  top <- get
  let Nothing := lookup nm top
    | _ => error fc "\{show nm} is already defined"
  putStrLn "-----"
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check (mkCtx top.metas) tm (VU fc)
  ty' <- nf [] ty
  putStrLn "got \{pprint [] ty'}"
  modify $ setDef nm ty' Axiom

processDecl (PType fc nm) = do
  ctx <- get
  modify $ setDef nm (U fc) PrimTCon
processDecl (PFunc fc nm ty src) = do
  top <- get
  ty <- check (mkCtx top.metas) ty (VU fc)
  ty' <- nf [] ty
  putStrLn "pfunc \{nm} : \{pprint [] ty'} := \{show src}"
  modify $ setDef nm ty' (PrimFn src)

processDecl (Def fc nm clauses) = do
  putStrLn "-----"
  putStrLn "def \{show nm}"
  ctx <- get
  let Just entry = lookup nm ctx
    | Nothing => throwError $ E fc "skip def \{nm} without Decl"
  let (MkEntry name ty Axiom) := entry
    | _ => throwError $ E fc "\{nm} already defined"

  -- and we pass to the case tree stuff now
  -- maybe fix up the clauses to match?
  -- Also we need to distinguish DCon/var

  putStrLn "check \{nm} ... at \{pprint [] ty}"
  vty <- eval empty CBN ty
  putStrLn "vty is \{show vty}"

  tm <- buildTree ({ fc := fc} $ mkCtx ctx.metas) (MkProb clauses vty)
  -- tm <- check (mkCtx ctx.metas) body vty
  putStrLn "Ok \{pprint [] tm}"

  mc <- readIORef ctx.metas
  for_ mc.metas $ \case
    (Solved k x) => pure ()
    (Unsolved (l,c) k xs) => do
      -- should just print, but it's too subtle in the sea of messages
      -- putStrLn "ERROR at (\{show l}, \{show c}): Unsolved meta \{show k}"
      throwError $ E (l,c) "Unsolved meta \{show k}"
  debug "Add def \{nm} \{pprint [] tm} : \{pprint [] ty}"
  modify $ setDef nm ty (Fn tm)

processDecl (DCheck fc tm ty) = do
  top <- get
  putStrLn "check \{show tm} at \{show ty}"
  ty' <- check (mkCtx top.metas) tm (VU fc)
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

processDecl (DImport fc str) = throwError $ E fc "import not implemented"

processDecl (Data fc nm ty cons) = do
  -- It seems like the FC for the errors are not here?
  ctx <- get
  tyty <- check (mkCtx ctx.metas) ty (VU fc)
  -- FIXME we need this in scope, but need to update
  modify $ setDef nm tyty Axiom
  ctx <- get
  cnames <- for cons $ \x => case x of
      -- expecting tm to be a Pi type
      (TypeSig fc nm' tm) => do
          ctx <- get
          dty <- check (mkCtx ctx.metas) tm (VU fc)
          debug "dty \{nm'} is \{pprint [] dty}"

          -- We only check that codomain uses the right type constructor
          -- We know it's in U because it's part of a checked Pi type
          let (codomain, tele) = splitTele dty
          -- for printing
          let tnames = reverse $ map (\(MkBind _ nm _ _) => nm) tele
          let (Ref _ hn _, args) := funArgs codomain
            | (tm, _) => error (getFC tm) "expected \{nm} got \{pprint tnames tm}"
          when (hn /= nm) $
            error (getFC codomain) "Constructor codomain is \{pprint tnames codomain} rather than \{nm}"

          modify $ setDef nm' dty (DCon (getArity dty) nm)
          pure nm'
      _ => throwError $ E (0,0) "expected constructor declaration"
  -- TODO check tm is VU or Pi ending in VU
  -- Maybe a pi -> binders function
  -- TODO we're putting in axioms, we need constructors
  -- for each constructor, check and add
  putStrLn "setDef \{nm}  TCon \{show cnames}"
  modify $ setDef nm tyty (TCon cnames)
  pure ()
  where
    checkDeclType : Tm -> M ()
    checkDeclType (U _) = pure ()
    checkDeclType (Pi _ str icit t u) = checkDeclType u
    checkDeclType _ = error fc "data type doesn't return U"
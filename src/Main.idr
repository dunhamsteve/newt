module Main

-- import Control.App
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Data.List
import Data.String
import Data.Vect
import Data.IORef
import Lib.Check
import Lib.Parser
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Token
import Lib.Tokenizer
import Lib.TopContext
import Lib.Types
import Lib.TT
import Syntax
import Syntax
import System
import System.Directory
import System.File

{-

Main2.idr has an older App attempt without the code below.

It has a repl, so we might want to re-integrate that code. And it uses
App, but we have a way to make that work on javascript.

I still want to stay in MonadError outside this file though.

-}


dumpContext : TopContext -> M ()
dumpContext top = do
    putStrLn "Context:"
    go top.defs
    putStrLn "---"
  where
    go : List TopEntry -> M ()
    go [] = pure ()
    go (x :: xs) = go xs >> putStrLn "    \{show x}"

processDecl : Decl -> M ()
processDecl (TypeSig nm tm) = do
  top <- get
  putStrLn "-----"
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check (mkCtx top.metas) tm VU
  ty' <- nf [] ty
  putStrLn "got \{show ty'}"
  modify $ claim nm ty'

-- FIXME - this should be in another file
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
  putStrLn "check \{nm} = \{show raw} at \{show $ ty}"
  vty <- eval empty CBN ty
  putStrLn "vty is \{show vty}"
  tm <- check (mkCtx ctx.metas) raw vty
  putStrLn "Ok \{show tm}"

  mc <- readIORef ctx.metas
  for_ mc.metas $ \case
    (Solved k x) => pure ()
    (Unsolved (l,c) k xs) => do
      -- putStrLn "ERROR at (\{show l}, \{show c}): Unsolved meta \{show k}"
      throwError $ E (l,c) "Unsolved meta \{show k}"

  put (addDef ctx nm tm ty)

processDecl (DCheck tm ty) = do

  top <- get
  putStrLn "check \{show tm} at \{show ty}"
  ty' <- check (mkCtx top.metas) tm VU
  putStrLn "got type \{show ty'}"
  vty <- eval [] CBN ty'
  res <- check (mkCtx top.metas) ty vty
  putStrLn "got \{show res}"
  norm <- nf [] res
  putStrLn "norm \{show norm}"
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
  -- TODO check tm is VU or Pi ending in VU
  -- Maybe a pi -> binders function
  -- TODO we're putting in axioms, we need constructors
  -- for each constructor, check and add
  modify $ claim nm tyty
  ctx <- get
  for_ cons $ \x => case x of
      -- expecting tm to be a Pi type
      (TypeSig nm' tm) => do
          ctx <- get
          -- TODO check pi type ending in full tyty application
          dty <- check (mkCtx ctx.metas) tm VU
          modify $ claim nm' dty
      _ => throwError $ E (0,0) "expected TypeSig"

  pure ()
  where
    checkDeclType : Tm -> M ()
    checkDeclType U = pure ()
    checkDeclType (Pi str icit t u) = checkDeclType u
    checkDeclType _ = throwError $ E (0,0) "data type doesn't return U"

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  Right src <- readFile $ fn
    | Left err => printLn err
  let toks = tokenise src
  let Right res = parse parseMod toks
    | Left y => putStrLn (showError src y)
  putStrLn $ render 80 $ pretty res
  printLn "process Decls"
  Right _ <- tryError $ traverse_ processDecl res.decls
    | Left y => putStrLn (showError src y)

  dumpContext !get

main' : M ()
main' = do
  args <- getArgs
  putStrLn "Args: \{show args}"
  let (_ :: files) = args
    | _ => putStrLn "Usage: newt foo.newt"
  -- Right files <- listDir "eg"
  --   | Left err => printLn err

  traverse_ processFile (filter (".newt" `isSuffixOf`) files)

main : IO ()
main = do
  -- we'll need to reset for each file, etc.
  ctx <- empty
  Right _  <- runEitherT $ runStateT ctx $ main'
    | Left (E (c, r) str) => putStrLn "Error: \{show c} \{show r} \{show str}"
  putStrLn "done"

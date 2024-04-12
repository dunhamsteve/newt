module Main

import Control.App
import Data.String
import Control.Monad.Error.Interface
import Control.Monad.Error.Either
import Control.Monad.State
import Lib.Check
import Lib.Parser
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Token
import Lib.Tokenizer
import Lib.TT
import Syntax
import Syntax
import System
import System.Directory
import System.File

{-

Currently working through checking of decl / def

Running check is awkward. I need a monad stack.
Main2.idr has an older App attempt without the code below. Retrofit.
-}

M : Type -> Type
M = (StateT Context (EitherT String IO))

processDecl : Decl -> M ()
processDecl (TypeSig nm tm) = do
  ctx <- get
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check ctx tm VU
  putStrLn "got \{show ty}"
  let vty = eval ctx.env ty
  putStrLn "--- \{show $ quote 0 vty}" 
  put $ extend ctx nm vty

processDecl (Def nm raw) = do
  putStrLn "def \{show nm}"
  ctx <- get
  let Just ty = lookup nm ctx.types
    | Nothing => printLn "skip def \{nm} without Decl"
  putStrLn "check \{nm} = \{show raw} at \{show $ quote 0 ty}"
  Right tm <- pure $ the (Either String Tm) (check ctx raw ty)
    | Left err => printLn err
  putStrLn "got \{show tm}"
  -- XXXXX here I need to update the environment
  -- I may want to rework things to have a top environment with names,
  -- then levels / indices for local stuff.
  
  
processDecl decl = putStrLn "skip \{show decl}"

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  Right src <- readFile $ "eg/" ++ fn
    | Left err => printLn err
  let toks = tokenise src
  let Right res = parse parseMod toks
    | Left y => putStrLn (showError src y)
  putStrLn $ pretty 80 $ pretty res
  printLn "process Decls"
  traverse_ processDecl res.decls
  putStrLn "done \{show !get}"

main' : M ()
main' = do
  args <- getArgs
  putStrLn "Args: \{show args}"

  Right files <- listDir "eg"
    | Left err => printLn err
  -- TODO use args
  
  traverse_ processFile (filter (".newt" `isSuffixOf`) files)

main : IO ()
main = do
  foo <- runEitherT $ runStateT TT.empty $ main'
  putStrLn "done"
    

module Main

import Control.App
import Data.String
import Data.Vect
import Data.List
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
import Lib.TopContext
import Syntax
import Syntax
import System
import System.Directory
import System.File

{-

- [ ] Replace on define
- [ ] more sugar on lambdas


Currently working through checking of decl / def

Running check is awkward. I need a monad stack.
Main2.idr has an older App attempt without the code below. Retrofit.

App isn't compatible with javascript (without a way to short circuit 
the fork foreign function.)

-}

M : Type -> Type
M = (StateT TopContext (EitherT String IO))

processDecl : Decl -> M ()
processDecl (TypeSig nm tm) = do
  ctx <- get
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check ctx empty tm VU
  putStrLn "got \{show ty}"
  
  put $ claim ctx nm ty

processDecl (Def nm raw) = do
  putStrLn "def \{show nm}"
  ctx <- get
  let Just entry = lookup nm ctx
    | Nothing => printLn "skip def \{nm} without Decl"
  let (MkEntry name ty Axiom) := entry
    -- FIXME error
    | _ => printLn "\{nm} already defined"
  putStrLn "check \{nm} = \{show raw} at \{show $ ty}"
  let vty = eval empty ty
  Right tm <- pure $ the (Either String Tm) (check ctx empty raw vty)
    | Left err => printLn err
  putStrLn "got \{show tm}"
  put (addDef ctx nm tm ty)
  
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
  foo <- runEitherT $ runStateT empty $ main'
  putStrLn "done"
    

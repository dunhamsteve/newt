module Main

-- import Control.App
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

Main2.idr has an older App attempt without the code below.

App was not compatible with javascript, but I have a remedy for
that now. 

-}

-- TODO We're shadowing Control.App.Error do we want that?

M : Type -> Type
M = (StateT TopContext (EitherT Impl.Error IO))


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
  ctx <- get
  putStrLn "TypeSig \{nm} \{show tm}"
  ty <- check ctx empty tm VU
  putStrLn "got \{show ty}"
  
  put $ claim ctx nm ty

processDecl (Def nm raw) = do
  putStrLn "def \{show nm}"
  ctx <- get
  let Just entry = lookup nm ctx
    | Nothing => throwError $ E (0,0) "skip def \{nm} without Decl"
  let (MkEntry name ty Axiom) := entry
    -- FIXME error
    | _ => throwError $ E (0,0) "\{nm} already defined"
  putStrLn "check \{nm} = \{show raw} at \{show $ ty}"
  let vty = eval empty CBN ty
  Right tm <- pure $ the (Either Impl.Error Tm) (check ctx empty raw vty)
    | Left err => throwError err
  putStrLn "Ok \{show tm}"
  put (addDef ctx nm tm ty)
  
processDecl decl = putStrLn "skip \{show decl}"

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
  Right _  <- runEitherT $ runStateT empty $ main'
    | Left (E (c, r) str) => putStrLn "Error: \{show c} \{show r} \{show str}"
  putStrLn "done"

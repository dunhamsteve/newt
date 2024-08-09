module Main

-- import Control.App
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Data.List
import Data.String
import Data.Vect
import Data.IORef
-- import Lib.Check
import Lib.Compile
import Lib.Parser
-- import Lib.Parser.Impl
import Lib.Prettier
import Lib.ProcessDecl
import Lib.Token
import Lib.Tokenizer
import Lib.TopContext
import Lib.Types
-- import Lib.TT
import Lib.Syntax
import Lib.Syntax
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

dumpSource : M ()
dumpSource = do
  doc <- compile
  putStrLn $ render 90 doc

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
  dumpSource

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

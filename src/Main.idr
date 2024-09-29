module Main

-- import Control.App
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Data.List
import Data.String
import Data.Vect
import Data.IORef
-- import Lib.Elab
import Lib.Compile
import Lib.Parser
-- import Lib.Parser.Impl
import Lib.Prettier
import Lib.ProcessDecl
import Lib.Token
import Lib.Tokenizer
import Lib.TopContext
import Lib.Types
import Lib.Syntax
import Lib.Syntax
import System
import System.Directory
import System.File
import System.Path

{-

import

need to find the file.
- get base directory
- . to /
- add .newt



loop back to processFile

-}

fail : String -> M a
fail msg = putStrLn msg >> exitFailure

dumpContext : TopContext -> M ()
dumpContext top = do
    putStrLn "Context:"
    go top.defs
    putStrLn "---"
  where
    go : List TopEntry -> M ()
    go [] = pure ()
    go (x :: xs) = putStrLn "    \{show x}" >> go xs

dumpSource : M ()
dumpSource = do
  doc <- compile
  putStrLn $ render 90 doc

parseFile : String -> M (String,Module)
parseFile fn = do
  Right src <- readFile $ fn
    | Left err => fail (show err)
  let toks = tokenise src
  let Right res = parse parseMod toks
    | Left y => fail (showError src y)
  pure (src, res)

loadModule : String -> String -> M ()
loadModule base name = do
  let fn = base ++ "/" ++ name ++ ".newt"
  (src, res) <- parseFile fn
  putStrLn "module \{res.name}"
  let True = name == res.name
    | _ => fail "module name \{show res.name} doesn't match file name \{show fn}"
  -- TODO separate imports and detect loops / redundant 
  for_ res.decls $ \ decl => case decl of
    (DImport x str) => loadModule base str
    _ => pure ()


  putStrLn "process Decls"
  Right _ <- tryError $ traverse_ processDecl (collectDecl res.decls)
    | Left y => fail (showError src y)

  pure ()

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  (src, res) <- parseFile fn
  putStrLn "module \{res.name}"
  let parts = splitPath fn
  let file = fromMaybe "" $ last' parts
  let dir = fromMaybe "./" $ parent fn
  let (base,ext) = splitFileName (fromMaybe "" $ last' parts)
  putStrLn "\{show dir} \{show base} \{show ext}"
  loadModule dir base
  top <- get
  dumpContext top
  dumpSource

  [] <- readIORef top.errors
    | errors => do
      for_ errors $ \err =>
        putStrLn (showError src err)
      exitFailure
  pure ()

main' : M ()
main' = do
  args <- getArgs
  putStrLn "Args: \{show args}"
  let (_ :: files) = args
    | _ => putStrLn "Usage: newt foo.newt"
  when ("-v" `elem` files) $ modify { verbose := True }
  traverse_ processFile (filter (".newt" `isSuffixOf`) files)

main : IO ()
main = do
  -- we'll need to reset for each file, etc.
  ctx <- empty
  Right _  <- runEitherT $ runStateT ctx $ main'
    | Left (E (c, r) str) => do
        putStrLn "ERROR at (\{show c}, \{show r}): \{show str}"
        exitFailure
  putStrLn "done"

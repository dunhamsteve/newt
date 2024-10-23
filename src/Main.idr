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


writeSource : String -> M ()
writeSource fn = do
  docs <- compile
  let src = unlines $ ["#!/usr/bin/env node"]
        ++ map (render 90) docs
        ++ [ "main();" ]
  Right _ <- writeFile fn src
    | Left err => fail (show err)
  Right _ <- chmodRaw fn 493 | Left err => fail (show err)
  pure ()

parseFile : String -> M (String,Module)
parseFile fn = do
  Right src <- readFile $ fn
    | Left err => fail (show err)
  let toks = tokenise src
  let Right res = parse parseMod toks
    | Left y => fail (showError src y)
  pure (src, res)

loadModule : String -> List String -> String -> M ()
loadModule base stk name = do
  top <- get
  -- already loaded?
  let False := elem name top.loaded | _ => pure ()
  modify { loaded $= (name::) }
  let fn = base ++ "/" ++ name ++ ".newt"
  (src, res) <- parseFile fn
  putStrLn "module \{res.name}"
  let True = name == res.name
    | _ => fail "ERROR at (0, 0): module name \{show res.name} doesn't match file name \{show fn}"
  -- TODO separate imports and detect loops / redundant
  for_ res.imports $ \ (MkImport fc name') => do
    -- we could use `fc` if it had a filename in it
    when (name' `elem` stk) $ error emptyFC "import loop \{show name} -> \{show name'}"
    loadModule base (name :: stk) name'

  -- TODO Lift the error exit, so import errors can get a FC in current file
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
  let (name,ext) = splitFileName (fromMaybe "" $ last' parts)
  putStrLn "\{show dir} \{show name} \{show ext}"
  loadModule dir [] name
  top <- get
  -- dumpContext top

  [] <- readIORef top.errors
    | errors => do
      for_ errors $ \err =>
        putStrLn (showError src err)
      exitFailure
  pure ()

cmdLine : List String -> M (Maybe String, List String)
cmdLine [] = pure (Nothing, [])
cmdLine ("-v" :: args) = do
  modify { verbose := True }
  cmdLine args
cmdLine ("-o" :: fn :: args) = do
  (out, files) <- cmdLine args
  pure (out <|> Just fn, files)

cmdLine (fn :: args) = do
  let True := ".newt" `isSuffixOf` fn
    | _ => error emptyFC "Bad argument \{show fn}"
  (out, files) <- cmdLine args
  pure $ (out, fn :: files)

main' : M ()
main' = do
  (arg0 :: args) <- getArgs
    | _ => error emptyFC "error reading args"
  (out, files) <- cmdLine args
  traverse_ processFile files
  case out of
    Nothing => pure ()
    Just name => writeSource name
  -- traverse_ processFile (filter (".newt" `isSuffixOf`) files) out

main : IO ()
main = do
  -- we'll need to reset for each file, etc.
  ctx <- empty
  Right _  <- runEitherT $ runStateT ctx $ main'
    | Left (E (c, r) str) => do
        putStrLn "ERROR at (\{show c}, \{show r}): \{show str}"
        exitFailure
  putStrLn "done"

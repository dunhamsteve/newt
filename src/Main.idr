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
import Lib.Elab
import Lib.Parser.Impl
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
  let src = unlines $
        [ "#!/usr/bin/env node"
        ,  "const PiType = (h0, h1) => ({ tag: \"PiType\", h0, h1 })" ]
        ++ map (render 90) docs
        ++ [ "main();" ]
  Right _ <- writeFile fn src
    | Left err => fail (show err)
  Right _ <- chmodRaw fn 493 | Left err => fail (show err)
  pure ()

||| New style loader, one def at a time
processModule : String -> List String -> String -> M String
processModule base stk name = do
  top <- get
  let False := elem name top.loaded | _ => pure ""
  modify { loaded $= (name::) }
  let fn = if base == "" then name ++ ".newt" else base ++ "/" ++ name ++ ".newt"
  Right src <- readFile $ fn
    | Left err => fail (show err)
  let Right toks = tokenise src
    | Left err => fail (showError src err)

  let Right ((nameFC, modName), ops, toks) := partialParse parseModHeader top.ops toks
    | Left err => fail (showError src err)


  putStrLn "module \{modName}"
  let True = name == modName
    | _ => fail "ERROR at \{show nameFC}: module name \{show modName} doesn't match file name \{show fn}"

  let Right (imports, ops, toks) := partialParse parseImports ops toks
    | Left err => fail (showError src err)

  for_ imports $ \ (MkImport fc name') => do
    -- we could use `fc` if it had a filename in it

    when (name' `elem` stk) $ error emptyFC "import loop \{show name} -> \{show name'}"
    processModule base (name :: stk) name'

  top <- get
  mc <- readIORef top.metas
  let mstart = length mc.metas
  let Right (decls, ops, toks) := partialParse (manySame parseDecl) top.ops toks
    | Left err => fail (showError src err)
  let [] := toks
    | (x :: xs) =>
        fail (showError src (E (startBounds x.bounds) "extra toks")) -- FIXME FC from xs
  modify { ops := ops }

  putStrLn "process Decls"
  Right _ <- tryError $ traverse_ processDecl (collectDecl decls)
    | Left y => fail (showError src y)
  if (stk == []) then logMetas mstart else pure ()
  pure src

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  let parts = splitPath fn
  let file = fromMaybe "" $ last' parts
  let dir = fromMaybe "./" $ parent fn
  let (name,ext) = splitFileName (fromMaybe "" $ last' parts)
  putStrLn "\{show dir} \{show name} \{show ext}"

  src <- processModule dir [] name
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

%export "javascript:newtMain"
main : IO ()
main = do
  -- we'll need to reset for each file, etc.
  ctx <- empty
  Right _  <- runEitherT $ runStateT ctx $ main'
    | Left err => do
        putStrLn "ERROR at \{show $ getFC err}: \{errorMsg err}"
        exitFailure
  putStrLn "done"

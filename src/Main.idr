module Main

-- import Control.App
import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.State
import Data.List
import Data.List1
import Data.String
import Data.Vect
import Data.IORef
-- import Lib.Elab
import Lib.Common
import Lib.Compile
import Lib.Parser
import Lib.Elab
import Lib.Parser.Impl
import Lib.Prettier
import Lib.ProcessDecl
import Lib.Token
import Lib.Tokenizer2
import Lib.TopContext
import Lib.Types
import Lib.Syntax
import Lib.Syntax
import System
import System.Directory
import System.File
import System.Path
import Data.Buffer

fail : String -> M a
fail msg = putStrLn msg >> exitFailure

jsonTopContext : M Json
jsonTopContext = do
  top <- get
  pure $ JsonObj [("context", JsonArray (map jsonDef $ toList top.defs))]
  where
    jsonDef : TopEntry -> Json
    -- There is no FC here...
    jsonDef (MkEntry fc (QN ns name) type def) = JsonObj
      [ ("fc", toJson fc)
      , ("name", toJson name)
      , ("type", toJson (render 80 $ pprint [] type) )
      ]

dumpContext : TopContext -> M ()
dumpContext top = do
    putStrLn "Context:"
    go $ toList top.defs
    putStrLn "---"
  where
    go : List TopEntry -> M ()
    go [] = pure ()
    go (x :: xs) = putStrLn "    \{show x}" >> go xs

writeSource : String -> M ()
writeSource fn = do
  docs <- compile
  let src = unlines $
        [ "\"use strict\";"
        ,  "const PiType = (h0, h1) => ({ tag: \"PiType\", h0, h1 })" ]
        ++ map (render 90) docs
  Right _ <- writeFile fn src
    | Left err => fail (show err)
  Right _ <- chmodRaw fn 493 | Left err => fail (show err)
  pure ()


parseDecls : String -> Operators -> TokenList -> SnocList Decl -> M (List Decl, Operators)
parseDecls fn ops [] acc = pure (acc <>> [], ops)
parseDecls fn ops toks@(first :: _) acc =
  case partialParse fn (sameLevel parseDecl) ops toks of
    Left (err, toks) => do
      putStrLn $ showError "" err
      addError err
      parseDecls fn ops (recover toks) acc
    Right (decl,ops,toks) => parseDecls fn ops toks (acc :< decl)
  where
    recover : TokenList -> TokenList
    recover [] = []
    -- skip to top token, but make sure there is progress
    recover (tok :: toks) = if tok.bounds.startCol == 0 && tok.bounds /= first.bounds
      then (tok :: toks)
      else recover toks

fastReadFile : HasIO io => String -> io (Either FileError String)
fastReadFile fn = do
  Right buf <- createBufferFromFile fn | Left err => pure $ Left err
  len <- rawSize buf
  Right <$> getString buf 0 len


||| New style loader, one def at a time
processModule : FC -> String -> List String -> String -> M String
processModule importFC base stk name = do
  top <- get
  let False := elem name top.loaded | _ => pure ""
  modify { loaded $= (name::) }
  let fn = if base == "" then name ++ ".newt" else base ++ "/" ++ name ++ ".newt"
  Right src <- fastReadFile $ fn
    | Left err => fail "ERROR at \{show importFC}: error reading \{fn}: \{show err}"
  let Right toks = tokenise fn src
    | Left err => fail (showError src err)

  let Right ((nameFC, modName), ops, toks) := partialParse fn parseModHeader top.ops toks
    | Left (err, toks) => fail (showError src err)


  putStrLn "module \{modName}"
  let True = name == modName
    | _ => fail "ERROR at \{show nameFC}: module name \{show modName} doesn't match file name \{show fn}"
  let ns = forget $ split (== '.') modName
  let Right (imports, ops, toks) := partialParse fn parseImports ops toks
    | Left (err, toks) => fail (showError src err)

  for_ imports $ \ (MkImport fc name') => do
    -- we could use `fc` if it had a filename in it

    when (name' `elem` stk) $ error emptyFC "import loop \{show name} -> \{show name'}"
    processModule fc base (name :: stk) name'

  top <- get
  mc <- readIORef top.metas
  -- REVIEW suppressing unsolved and solved metas from previous files
  -- I may want to know about (or fail early on) unsolved
  let mstart = length mc.metas
  -- let Right (decls, ops, toks) := partialParse fn (manySame parseDecl) top.ops toks
  --   | Left (err, toks) => fail (showError src err)
  (decls, ops) <- parseDecls fn top.ops toks [<]
  modify { ops := ops }

  putStrLn "process Decls"

  traverse_ (tryProcessDecl ns) (collectDecl decls)

  -- we don't want implict errors from half-processed functions
  -- but suppress them all on error for simplicity.
  errors <- readIORef top.errors
  if stk == [] && length errors == 0 then logMetas mstart else pure ()
  pure src
  where

    -- parseDecls :
    -- tryParseDecl :
    tryProcessDecl : List String -> Decl -> M ()
    tryProcessDecl ns decl = do
      Left err <- tryError {e=Error} $ processDecl ns decl | _ => pure ()
      addError err

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  let parts = split (== '/') fn
  let file = last parts
  let dirs = init parts
  let dir = if dirs == Nil then "." else joinBy "/" dirs
  let (name,ext) = splitFileName file
  putStrLn "\{show dir} \{show name} \{show ext}"

  -- declare internal primitives
  processDecl ["Prim"] (PType emptyFC "Int" Nothing)
  processDecl ["Prim"] (PType emptyFC "String" Nothing)
  processDecl ["Prim"] (PType emptyFC "Char" Nothing)

  src <- processModule emptyFC dir [] name
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
cmdLine ("--top" :: args) = cmdLine args -- handled later
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

  when (elem "--top" args) $ putStrLn "TOP:\{renderJson !jsonTopContext}"

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

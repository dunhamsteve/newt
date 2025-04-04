module Main

import Data.List
import Data.List1
import Data.String
import Data.Vect
import Data.IORef
import Lib.Common
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
        , "const PiType = (h0, h1) => ({ tag: \"PiType\", h0, h1 })"
        , "const U = { tag: \"U\" };"
        ] ++ map (render 90) docs
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
processModule : FC -> String -> List String -> QName -> M String
processModule importFC base stk qn@(QN ns nm) = do
  top <- get
  -- TODO make top.loaded a List QName
  let name = joinBy "." (snoc ns nm)
  let False := elem name top.loaded | _ => pure ""
  modify { loaded $= (name::) }
  let fn = (String.joinBy "/" (base :: ns)) ++ "/" ++ nm ++ ".newt"
  Right src <- fastReadFile $ fn
    | Left err => fail "ERROR at \{show importFC}: error reading \{fn}: \{show err}"
  let Right toks = tokenise fn src
    | Left err => fail (showError src err)

  let Right ((nameFC, modName), ops, toks) := partialParse fn parseModHeader top.ops toks
    | Left (err, toks) => fail (showError src err)

  putStrLn "module \{modName}"
  let ns = forget $ split (== '.') modName
  let (path, modName') = unsnoc $ split (== '.') modName
  let bparts = split (== '/') base
  let True = qn == QN path modName'
    | _ => fail "ERROR at \{show nameFC}: module name \{show modName} doesn't match file name \{show fn}"

  let Right (imports, ops, toks) := partialParse fn parseImports ops toks
    | Left (err, toks) => fail (showError src err)

  for_ imports $ \ (MkImport fc name') => do
    let (a,b) = unsnoc $ split (== '.') name'
    let qname = QN a b
    -- we could use `fc` if it had a filename in it
    when (name' `elem` stk) $ error emptyFC "import loop \{show name} -> \{show name'}"

    processModule fc base (name :: stk) qname

  top <- get
  mc <- readIORef top.metaCtx
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
  [] <- readIORef top.errors
    | errors => do
      for_ errors $ \err =>
        putStrLn (showError src err)
      exitFailure

  if stk == [] then logMetas mstart else pure ()
  pure src
  where

    -- parseDecls :
    -- tryParseDecl :
    tryProcessDecl : List String -> Decl -> M ()
    tryProcessDecl ns decl = do
      Left err <- tryError $ processDecl ns decl | _ => pure ()
      addError err

processFile : String -> M ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  let parts = split (== '/') fn
  let (dirs,file) = unsnoc parts
  let dir = if dirs == Nil then "." else joinBy "/" dirs
  let (name,ext) = splitFileName file
  putStrLn "\{show dir} \{show name} \{show ext}"

  top <- get
  Right src <- fastReadFile $ fn
    | Left err => fail "ERROR at \{fn}:(0, 0): error reading \{fn}: \{show err}"
  let Right toks = tokenise fn src
    | Left err => fail (showError src err)
  let Right ((nameFC, modName), ops, toks) := partialParse fn parseModHeader top.ops toks
    | Left (err, toks) => fail (showError src err)
  let ns = forget $ split (== '.') modName
  let (path, modName') = unsnoc $ split (== '.') modName
  let True = modName' == name
    | False => fail "ERROR at \{fn}:(0, 0): module name \{modName'} doesn't match \{name}"
  let Right base = baseDir (Lin <>< dirs) (Lin <>< path)
    | Left err => fail "ERROR at \{show nameFC}: \{err}"
  let base = if base == "" then "." else base
  -- declare internal primitives
  processDecl ["Prim"] (PType emptyFC "Int" Nothing)
  processDecl ["Prim"] (PType emptyFC "String" Nothing)
  processDecl ["Prim"] (PType emptyFC "Char" Nothing)

  src <- processModule emptyFC base [] (QN path modName')
  top <- get
  -- dumpContext top

  [] <- readIORef top.errors
    | errors => do
      for_ errors $ \err =>
        putStrLn (showError src err)
      exitFailure
  pure ()

  where
    baseDir : SnocList String -> SnocList String -> Either String String
    baseDir dirs Lin = Right $ joinBy "/" (dirs <>> [])
    baseDir (dirs :< d) (ns :< n) = if d == n
      then baseDir dirs ns
      else Left "module path doesn't match directory"
    baseDir Lin _ = Left "module path doesn't match directory"

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
  Right _  <- runM main' ctx
    | Left err => do
        putStrLn "ERROR at \{show $ getFC err}: \{errorMsg err}"
        exitFailure
  putStrLn "done"

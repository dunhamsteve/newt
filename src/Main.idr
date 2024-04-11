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

M = MonadError (String) (StateT Context IO)

processDecl : Context -> Decl -> IO Context
processDecl ctx (TypeSig nm tm)= do
  putStrLn "TypeSig \{nm} \{show tm}"
  Right ty <- pure $ the (Either String Tm) (check ctx tm VU)
    | Left err => printLn err >> pure ctx
  let vty = eval ctx.env ty
  pure $ extend ctx nm vty
processDecl ctx (Def nm raw) = do
  putStrLn "def \{show nm}"
  let Just ty = lookup nm ctx.types
    | Nothing => printLn "skip def \{nm} without Decl" >> pure ctx
  putStrLn "check \{nm} \{show raw} at [no printer for Tm/Val]"
  Right ty <- pure $ the (Either String Tm) (check ctx raw ty)
    | Left err => printLn err >> pure ctx
  pure ctx
processDecl ctx decl = putStrLn "skip \{show decl}" >> pure ctx

processFile : String -> IO ()
processFile fn = do
  putStrLn "*** Process \{fn}"
  Right src <- readFile $ "eg/" ++ fn
    | Left err => printLn err
  let toks = tokenise src
  let Right res = parse parseMod toks
    | Left y => putStrLn (showError src y)
  putStrLn $ pretty 80 $ pretty res
  printLn "process Decls"
  ctx <- foldlM processDecl empty res.decls
  putStrLn "done \{show ctx}"


main : IO ()
main = do
  args <- getArgs
  putStrLn "Args: \{show args}"
  Right files <- listDir "eg"
    | Left err => printLn err
  -- TODO use args
  traverse_ processFile (filter (".newt" `isSuffixOf`) files)


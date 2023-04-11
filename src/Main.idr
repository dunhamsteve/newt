module Main

import Data.String
import Lib.Tokenizer
-- import Lib.Layout
import Lib.Token
import Lib.Parser.Impl
import Lib.Parser
import Syntax
import System
import System.File
import System.Directory
import Control.App

-- Put stuff in attic
-- Error printing
-- Review surface syntax
-- Prettier printer
-- First pass at typecheck
-- Just do it in zoo order


-- showPError : String -> 

test : Show a => Parser a -> String -> IO ()
test pa src = do
  _ <- putStrLn "--"
  _ <- putStrLn $ src
  let toks = tokenise src
  putStrLn "- Toks"
  printLn $ toks
  putStrLn "- Parse"
  let res = parse pa toks
  printLn res
  -- let toks2 = layout toks
  -- printLn $ map value toks2

-- gotta fix up error messages. Show it with some source

testFile : String -> IO ()
testFile fn = do
  putStrLn ("***" ++ fn)
  Right text <- readFile $ "eg/" ++ fn
    | Left err => printLn err
  test parseMod text

olderTests : IO ()
olderTests = do
  test letExpr "let x = 1\n    y = 2\n in x + y"
  test term "let x = 1 in x + 2"
  printLn "BREAK"
  test term "case x of\n   True => something\n   False => let\n      x = 1\n      y = 2\n    in x + y"
  test term "x + y * z + w"
  test term "y * z + w"
  test term "x -> y -> z"
  test term "x y z"
  test parseMod "module Foo\nfoo : Int -> Int\nfoo = \\ x . x"
  test lamExpr "\\ x . x"
  test parseMod "module Foo\nimport Foo.Bar\nfoo = 1\n"
  test parseDef "foo = 1"
  test parseSig "foo : Bar -> Int"
  test parseMod "module Test\nid : a -> a\nid = \\ x => x\n"

foo : Maybe Int -> Int
foo Nothing = ?foo_rhs_0
foo (Just x) = ?foo_rhs_1


main : IO ()
main = do
  Right files <- listDir "eg"
    | Left err => printLn err
  traverse_ testFile (filter (".newt" `isSuffixOf`) files)
  

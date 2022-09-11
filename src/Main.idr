module Main

import Lib.Tokenizer
import Lib.Layout
import Lib.Token
import Lib.Parser.Impl
import Lib.Parser
import Syntax

check : Show a => Parser a -> String -> IO ()
check pa src = do
  _ <- putStrLn "--"
  _ <- putStrLn $ src
  let toks = tokenise src
  printLn $ toks
  let res = parse pa toks
  printLn res
  -- let toks2 = layout toks
  -- printLn $ map value toks2

-- gotta fix up error messages. Show it with some source

main : IO ()
main = do
  -- this stuff is working with layout, should I bother with col.
  -- downside is that it will be somewhat picky about the indentation of `in`
  -- The sixty stuff looks promising.  I might want my own tokenizer though.
  check letExpr "let x = 1\n    y = 2\n in x + y"
  check term "let x = 1 in x + 2"
  printLn "BREAK"
  check term "case x of\n   True => something\n   False => let\n      x = 1\n      y = 2\n    in x + y"
  check term "x + y * z + w"
  check term "y * z + w"
  check term "x -> y -> z"
  check term "x y z"

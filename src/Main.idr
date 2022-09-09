module Main

import Lib.Tokenizer
import Lib.Layout
import Lib.Token

src = "let x = 1\n    y = 2\n in x + y"

check : String -> IO ()
check src = do
  putStrLn "--"
  printLn $ src
  let toks = tokenise src
  
  printLn $ toks
  let toks2 = layout toks
  
  printLn $ map value toks2

main : IO ()
main = do
  -- this stuff is working with layout, should I bother with col.
  -- downside is that it will be somewhat picky about the indentation of `in`
  -- The sixty stuff looks promising.  I might want my own tokenizer though.
  check "let x = 1\n    y = 2\n in x + y"
  check "let x = 1 in x + 2"
  check "case x of\n   True => something\n   False => let\n      x = 1\n      y = 2\n    in x + y"


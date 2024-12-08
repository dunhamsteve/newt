module Main

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Lib.Types
import Lib.ProcessDecl
import Lib.TopContext
import Lib.Syntax

{-

Expect these to throw. (need failing blocks or a white box test here)
After we get pack/lsp issues sorted with this directory

foo : Maybe (Int × Int) -> Int
foo 1 = ?
foo _ = ?

foo : Maybe (Int × Int) -> Int
foo (1,1) = ?
foo _ = ?

-}

testCase : M ()
testCase = do
  -- need to get some defs in here
  top <- get
  let ctx = mkCtx top.metas
  let e = emptyFC
  -- maybe easier to parse out this data.
  processDecl (Data e "Foo" (RU e) [])

  tree <- buildTree ctx (MkProb [] (VU emptyFC))
  --ty <- check (mkCtx top.metas) tm (VU fc)
  pure ()


main : IO ()
main = do
  -- TODO move the tests elsewhere
  -- We'll need a new top, start an M, maybe push a few things in there
  -- run buildTree and see what we get back
    ctx <- empty
    Right _ <- runEitherT $ runStateT ctx $ testCase
      | Left (E fc msg) => putStrLn "Error: \{msg}"
    putStrLn "done"
    pure ()
-- A telescope is a list of binders, right? I've been leaving things as pi types to be explicit

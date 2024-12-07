module Lib.TopContext

import Data.String
import Lib.Types
import Data.IORef

-- I want unique ids, to be able to lookup, update, and a Ref so
-- I don't need good Context discipline. (I seem to have made mistakes already.)

export
lookup : String -> TopContext -> Maybe TopEntry
lookup nm top = go top.defs
  where
    go : List TopEntry -> Maybe TopEntry
    go [] = Nothing
    go (entry :: xs) = if entry.name == nm then Just entry else go xs

-- Maybe pretty print?
export
covering
Show TopContext where
  show (MkTop defs metas _ _ _ _) = "\nContext:\n [\{ joinBy "\n" $ map show defs}]"

public export
empty : HasIO m => m TopContext
empty = pure $ MkTop [] !(newIORef (MC [] 0)) False !(newIORef []) [] empty

||| set or replace def. probably need to check types and Axiom on replace
-- public export
-- setDef : String -> Tm -> Def -> TopContext -> TopContext
-- setDef name ty def = { defs $= go }
--   where
--     go : List TopEntry -> List TopEntry
--     go [] = [MkEntry name ty def]
--     go (x@(MkEntry nm ty' def') :: defs) = if nm == name
--       then MkEntry name ty def :: defs
--       else x :: go defs

public export
setDef : String -> FC -> Tm -> Def -> M ()
setDef name fc ty def = do
  top <- get
  defs <- go top.defs
  put $ { defs := defs } top
  where
    go : List TopEntry -> M (List TopEntry)
    go [] = pure $ [MkEntry fc name ty def]
    go (x@(MkEntry _ nm ty' def') :: defs) = if nm == name
      then error fc "\{name} is already defined"
      else (x ::) <$> go defs

public export
updateDef : String -> FC -> Tm -> Def -> M ()
updateDef name fc ty def = do
  top <- get
  defs <- go top.defs
  put $ { defs := defs } top
  where
    go : List TopEntry -> M (List TopEntry)
    go [] = error fc "\{name} not declared"
    go (x@(MkEntry fc' nm ty' def') :: defs) = if nm == name
      -- keep original fc, so it points to the TypeSig
      then pure $ MkEntry fc' name ty def :: defs
      else (x ::) <$> go defs


public export
addError : HasIO io => {auto top : TopContext} -> Error -> io ()
addError err = modifyIORef top.errors (err ::)

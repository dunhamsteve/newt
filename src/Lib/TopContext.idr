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
  show (MkTop defs metas _ _ _) = "\nContext:\n [\{ joinBy "\n" $ map show defs}]"

public export
empty : HasIO m => m TopContext
empty = pure $ MkTop [] !(newIORef (MC [] 0)) False !(newIORef []) []

||| set or replace def. probably need to check types and Axiom on replace
public export
setDef : String -> Tm -> Def -> TopContext -> TopContext
setDef name ty def = { defs $= go }
  where
    go : List TopEntry -> List TopEntry
    go [] = [MkEntry name ty def]
    go (x@(MkEntry nm ty' def') :: defs) = if nm == name
      then MkEntry name ty def :: defs
      else x :: go defs

public export
addError : HasIO io => {auto top : TopContext} -> Error -> io ()
addError err = modifyIORef top.errors (err ::)

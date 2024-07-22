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
Show TopContext where
  show (MkTop defs metas _) = "\nContext:\n [\{ joinBy "\n" $ map show defs}]"

public export
empty : HasIO m => m TopContext
empty = pure $ MkTop [] !(newIORef (MC [] 0)) True

public export
claim : String -> Tm -> TopContext -> TopContext
claim name ty = { defs $= (MkEntry name ty Axiom ::) }

-- TODO update existing, throw, etc.

public export
addDef : TopContext -> String -> Tm -> Tm -> TopContext
addDef tc name tm ty = { defs $= go } tc
  where
    go : List TopEntry -> List TopEntry
    -- FIXME throw if we hit [] or is not an axiom
    go [] = []
    go ((MkEntry nm _ _) :: xs) = MkEntry nm ty (Fn tm) :: xs


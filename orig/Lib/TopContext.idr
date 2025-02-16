module Lib.TopContext

import Data.IORef
import Data.SortedMap
import Data.String
import Lib.Types

-- I want unique ids, to be able to lookup, update, and a Ref so
-- I don't need good Context discipline. (I seem to have made mistakes already.)

export
lookup : QName -> TopContext -> Maybe TopEntry
lookup nm top = lookup nm top.defs

-- TODO - look at imported namespaces, and either have a map of imported names or search imported namespaces..
export
lookupRaw : String -> TopContext -> Maybe TopEntry
lookupRaw raw top = go $ toList top.defs
  where
    go : List (QName, TopEntry) -> Maybe TopEntry
    go Nil = Nothing
    go (((QN ns nm), entry) :: rest) = if nm == raw then Just entry else go rest

-- Maybe pretty print?
export
covering
Show TopContext where
  show (MkTop defs metas _ _ _ _) = "\nContext:\n [\{ joinBy "\n" $ map (show . snd) $ toList defs}]"

public export
empty : HasIO m => m TopContext
empty = pure $ MkTop empty !(newIORef (MC [] 0 CheckAll)) False !(newIORef []) [] empty

public export
setDef : QName -> FC -> Tm -> Def -> M ()
setDef name fc ty def = do
  top <- get
  let Nothing = lookup name top.defs
    | Just (MkEntry fc' nm' ty' def') => error fc "\{name} is already defined at \{show fc'}"
  put $ { defs $= (insert name (MkEntry fc name ty def)) } top

public export
updateDef : QName -> FC -> Tm -> Def -> M ()
updateDef name fc ty def = do
  top <- get
  let Just (MkEntry fc' nm' ty' def') = lookup name top.defs
    | Nothing => error fc "\{name} not declared"
  put $ { defs $= (insert name (MkEntry fc' name ty def)) } top

public export
addError : Error -> M ()
addError err = do
  top <- get
  modifyIORef top.errors (err ::)

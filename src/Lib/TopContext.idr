module Lib.TopContext

import Data.String
import Lib.TT


public export
data Def = Axiom | TCon (List String) | DCon Nat | Fn Tm

Show Def where
  show Axiom = "axiom"
  show (TCon strs) = "TCon \{show strs}"
  show (DCon k) = "DCon \{show k}"
  show (Fn t) = "Fn \{show t}"

||| entry in the top level context
public export
record TopEntry where
  constructor MkEntry
  name : String
  type : Tm
  def : Def

-- FIXME snoc

export
Show TopEntry where
  show (MkEntry name type def) = "\{name} : \{show type} := \{show def}"

||| Top level context.
||| Most of the reason this is separate is to have a different type
||| `Def` for the entries.
|||
||| The price is that we have names in addition to levels. Do we want to
||| expand these during conversion?
public export
record TopContext where
  constructor MkTop
  -- We'll add a map later?
  defs : List TopEntry


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
  show (MkTop defs) = "\nContext:\n [\{ joinBy "\n" $ map show defs}]"

public export
empty : TopContext
empty = MkTop []

public export
claim : TopContext -> String -> Tm -> TopContext
claim tc name ty = { defs $= (MkEntry name ty Axiom ::) } tc

-- TODO update existing, throw, etc.

public export
addDef : TopContext -> String -> Tm -> Tm -> TopContext
addDef tc name tm ty = { defs $= go } tc
  where
    go : List TopEntry -> List TopEntry
    -- FIXME throw if we hit [] or is not an axiom
    go [] = []
    go ((MkEntry nm _ _) :: xs) = MkEntry nm ty (Fn tm) :: xs


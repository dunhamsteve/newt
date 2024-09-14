module Lib.Util

import Lib.Types

export
funArgs : Tm -> (Tm, List Tm)
funArgs tm = go tm []
  where
    go : Tm -> List Tm -> (Tm, List Tm)
    go (App _ t u) args = go t (u :: args)
    go t args = (t, args)


public export
data Binder : Type where
  MkBind : FC -> String -> Icit -> Tm -> Binder

-- I don't have a show for terms without a name list
export
Show Binder where
  show (MkBind _ nm icit t) = "[\{nm} \{show icit} : ...]"

data Foo : Type -> Type where
  MkFoo : Nat -> Foo a

export
splitTele : Tm -> (Tm, List Binder)
splitTele = go []
  where
    go : List Binder -> Tm -> (Tm, List Binder)
    go ts (Pi fc nm icit t u) = go (MkBind fc nm icit t :: ts) u
    go ts tm = (tm, reverse ts)

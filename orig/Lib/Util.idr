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
  MkBinder : FC -> String -> Icit -> Quant -> Tm -> Binder

-- I don't have a show for terms without a name list
export
Show Binder where
  show (MkBinder _ nm icit quant t) = "[\{show quant}\{nm} \{show icit} : ...]"

export
splitTele : Tm -> (Tm, List Binder)
splitTele = go []
  where
    go : List Binder -> Tm -> (Tm, List Binder)
    go ts (Pi fc nm icit quant t u) = go (MkBinder fc nm icit quant t :: ts) u
    go ts tm = (tm, reverse ts)

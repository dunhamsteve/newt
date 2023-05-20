module Lib.Check

import Lib.Parser.Impl
import Lib.TT


record Cxt where
  env : List Val

  pos : SourcePos

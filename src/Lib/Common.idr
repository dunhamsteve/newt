module Lib.Common

import Data.String
import public Data.SortedMap


public export
record FC where
  constructor MkFC
  file : String
  start : (Int,Int)

export
(.line) : FC -> Int
fc.line = fst fc.start

export
(.col) : FC -> Int
fc.col = snd fc.start

public export
interface HasFC a where
  getFC : a -> FC

%name FC fc

export
emptyFC : FC
emptyFC = MkFC "" (0,0)

-- Error of a parse
public export
data Error
  = E FC String
  | Postpone FC Nat String
%name Error err

export
Show FC where
  show fc = "\{fc.file}:\{show fc.start}"

public export
showError : String -> Error -> String
showError src (E fc msg) = "ERROR at \{show fc}: \{msg}\n" ++ go 0 (lines src)
  where
    go : Int -> List String -> String
    go l [] = ""
    go l (x :: xs) =
      if l == fc.line then
        "  \{x}\n  \{replicate (cast fc.col) ' '}^\n"
      else if fc.line - 3 < l then "  " ++ x ++ "\n" ++ go (l + 1) xs
      else go (l + 1) xs
showError src (Postpone fc ix msg) = "ERROR at \{show fc}: Postpone \{show ix} \{msg}\n" ++ go 0 (lines src)
  where
    go : Int -> List String -> String
    go l [] = ""
    go l (x :: xs) =
      if l == fc.line then
        "  \{x}\n  \{replicate (cast fc.col) ' '}^\n"
      else if fc.line - 3 < l then "  " ++ x ++ "\n" ++ go (l + 1) xs
      else go (l + 1) xs

public export
data Fixity = InfixL | InfixR | Infix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix = "infix"


public export
record OpDef where
  constructor MkOp
  name : String
  prec : Int
  fix : Fixity
  isPrefix : Bool
  ||| rule is everything after the first part of the operator, splitting on `_`
  ||| a normal infix operator will have a trailing `""` which will match to
  ||| prec / prec - 1
  rule : List String

public export
Operators : Type
Operators = SortedMap String OpDef

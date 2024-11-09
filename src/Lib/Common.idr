module Lib.Common

import Data.String

-- I was going to use a record, but we're peeling this off of bounds at the moment.
public export
FC : Type
FC = (Int,Int)

public export
interface HasFC a where
  getFC : a -> FC

%name FC fc

export
emptyFC : FC
emptyFC = (0,0)

-- Error of a parse
public export
data Error
  = E FC String
  | Postpone FC Nat String
%name Error err

public export
showError : String -> Error -> String
showError src (E (line, col) msg) = "ERROR at \{show (line,col)}: \{msg}\n" ++ go 0 (lines src)
  where
    go : Int -> List String -> String
    go l [] = ""
    go l (x :: xs) =
      if l == line then
        "  \{x}\n  \{replicate (cast col) ' '}^\n"
      else if line - 3 < l then "  " ++ x ++ "\n" ++ go (l + 1) xs
      else go (l + 1) xs
showError src (Postpone (line, col) ix msg) = "ERROR at \{show (line,col)}: Postpone \{show ix} \{msg}\n" ++ go 0 (lines src)
  where
    go : Int -> List String -> String
    go l [] = ""
    go l (x :: xs) =
      if l == line then
        "  \{x}\n  \{replicate (cast col) ' '}^\n"
      else if line - 3 < l then "  " ++ x ++ "\n" ++ go (l + 1) xs
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


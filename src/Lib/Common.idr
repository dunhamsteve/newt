module Lib.Common

import Data.String
import Data.Nat
import Data.Maybe
import public Data.SortedMap

hexChars : List Char
hexChars = unpack "0123456789ABCDEF"

-- export
hexDigit : Nat -> Char
hexDigit v = fromMaybe ' ' (getAt (mod v 16) hexChars)

export
toHex : Nat -> List Char
toHex 0 = []
toHex v = snoc (toHex (div v 16)) (hexDigit v)

export
quoteString : String -> String
quoteString str = pack $ encode (unpack str) [< '"']
  where
    encode : List Char -> SnocList Char -> List Char
    encode [] acc = acc <>> ['"']
    encode ('"' :: cs) acc = encode cs (acc :< '\\' :< '"')
    encode ('\n' :: cs) acc = encode cs (acc :< '\\' :< 'n')
    encode ('\\' :: cs) acc = encode cs (acc :< '\\' :< '\\')
    encode (c :: cs) acc =
      let v : Nat = cast c in
      if v < 32 then encode cs (acc :< '\\' :< 'u' :< hexDigit (div v 4096) :< hexDigit (div v 256) :< hexDigit (div v 16) :< hexDigit v )
      else encode cs (acc :< c)
      -- else if v < 128 then encode cs (acc :< c)
      -- if v < 32 then encode cs (acc :< '\\' :< 'x' :< hexDigit (div v 16) :< hexDigit v )
      -- else if v < 128 then encode cs (acc :< c)
      -- -- TODO unicode
      -- else if v < 256 then encode cs (acc :< '\\' :< 'x' :< hexDigit (div v 16) :< hexDigit v )
      -- else encode cs (acc :< '\\' :< 'u' :< hexDigit (div v 4096) :< hexDigit (div v 256) :< hexDigit (div v 16) :< hexDigit v )

public export
data Json : Type where
  JsonObj : List (String, Json) -> Json
  JsonStr : String -> Json
  JsonBool : Bool -> Json
  JsonInt : Int -> Json
  JsonArray : List Json -> Json

export
renderJson : Json -> String
renderJson (JsonObj xs) = "{" ++ joinBy "," (map renderPair xs) ++ "}"
  where
    renderPair : (String,Json) -> String
    renderPair (k,v) = quoteString k ++ ":" ++ renderJson v
renderJson (JsonStr str) = quoteString str
renderJson (JsonBool x) = ifThenElse x "true" "false"
renderJson (JsonInt i) = cast i
renderJson (JsonArray xs) = "[" ++ joinBy "," (map renderJson xs) ++ "]"

public export
interface ToJSON a where
  toJson : a -> Json

export
ToJSON String where
  toJson = JsonStr

export
ToJSON Int where
  toJson = JsonInt

public export
record FC where
  constructor MkFC
  file : String
  start : (Int,Int)

export
ToJSON FC where
  toJson (MkFC file (line,col)) = JsonObj [ ("file", toJson file), ("line", toJson line), ("col", toJson col)]

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

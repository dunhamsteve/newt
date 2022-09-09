module Lib.Tok2

import Text.Bounded

data Kind 
  = Ident 
  | Keyword 
  | Oper 
  | Number 
  | Symbol
  | Arrow
  | Ignore
  | EOF

data Token = Tok Kind String

Show Kind where
  show Ident   = "Ident"
  show Keyword = "Keyword"
  show Oper    = "Oper"
  show Number  = "Number"
  show Symbol  = "Symbol"
  show Arrow   = "Arrow"
  show Ignore  = "Ignore"
  show EOF = "EOF"

Show Token where show (Tok k v) = "<\{show k}:\{show v}>"

keywords : List String
keywords = ["let", "in", "where", "case"]

specialOps : List String
specialOps = ["->", ":"]

checkKW : String -> Token
checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

opkind : String -> Kind
opkind "->" = Arrow
opkind _    = Oper

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

nextToken : Int -> Int -> List Char -> Maybe (Token, (Int, Int, List Char))
nextToken row col xs = case xs of
  []  => Nothing
  (' ' :: cs) =>  nextToken row (col + 1) cs
  (c :: cs)   =>
    if isDigit c then getTok (Tok Number) isDigit [c] cs
    else if isOpChar c then getTok else ?Foo
  where
    getTok : (String -> Token) -> (Char -> Bool) -> List Char -> List Char -> Maybe (Token, (Int, Int, List Char))



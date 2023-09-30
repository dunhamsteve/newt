module Lib.Token

import public Text.Lexer

public export
data Kind 
  = Ident 
  | Keyword 
  | Oper 
  | Number 
  | Symbol
  | Space
  | Comment
  | Pragma
  -- not doing Layout.idr
  | LBrace
  | Semi
  | RBrace
  | EOI

export
Show Kind where
  show Ident   = "Ident"
  show Keyword = "Keyword"
  show Oper    = "Oper"
  show Number  = "Number"
  show Symbol  = "Symbol"
  show Space  = "Space"
  show LBrace  = "LBrace"
  show Semi    = "Semi"
  show RBrace  = "RBrace"
  show Comment = "Comment"
  show EOI     = "EOI"
  show Pragma  = "Pragma"
export
Eq Kind where
  Ident   == Ident = True
  Keyword == Keyword = True
  Oper    == Oper = True
  Number  == Number = True
  Symbol  == Symbol = True
  Space   == Space = True
  LBrace  == LBrace = True
  Semi    == Semi   = True
  RBrace  == RBrace = True
  _ == _ = False

export
Show k => Show (Token k) where
  show (Tok k v) = "<\{show k}:\{show v}>"

public export
BTok : Type
BTok = WithBounds (Token Kind)

export
value : BTok -> String
value (MkBounded (Tok _ s) _ _) = s

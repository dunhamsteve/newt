module Lib.Token

-- TODO replace this with own lexer

import public Text.Lexer

public export
data Kind
  = Ident
  | UIdent
  | Keyword
  | Oper
  | MixFix
  | Number
  | Character
  | StringKind
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
  show UIdent   = "UIdent"
  show Keyword = "Keyword"
  show Oper    = "Oper"
  show MixFix = "MixFix"
  show Number  = "Number"
  show Character  = "Character"
  show Symbol  = "Symbol"
  show Space  = "Space"
  show LBrace  = "LBrace"
  show Semi    = "Semi"
  show RBrace  = "RBrace"
  show Comment = "Comment"
  show EOI     = "EOI"
  show Pragma  = "Pragma"
  show StringKind = "String"
export
Eq Kind where
  Ident   == Ident = True
  UIdent  == UIdent = True
  Keyword == Keyword = True
  Oper    == Oper = True
  MixFix  == MixFix = True
  Number  == Number = True
  Character == Character = True
  Symbol  == Symbol = True
  Space   == Space = True
  LBrace  == LBrace = True
  Semi    == Semi   = True
  RBrace  == RBrace = True
  StringKind == StringKind = True
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

export
kind : BTok -> Kind
kind (MkBounded (Tok k s) _ _) = k

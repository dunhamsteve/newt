module Lib.Token

public export
record Bounds where
  constructor MkBounds
  startLine : Int
  startCol : Int
  endLine : Int
  endCol : Int

export
Eq Bounds where
  (MkBounds sl sc el ec) == (MkBounds sl' sc' el' ec') =
      sl == sl'
   && sc == sc'
   && el == el'
   && ec == ec'

public export
record WithBounds ty where
  constructor MkBounded
  val : ty
  bounds : Bounds

public export
data Kind
  = Ident
  | UIdent
  | Keyword
  | MixFix
  | Number
  | Character
  | StringKind
  | JSLit
  | Symbol
  | Space
  | Comment
  | Pragma
  | Projection
  -- not doing Layout.idr
  | LBrace
  | Semi
  | RBrace
  | EOI
  | StartQuote
  | EndQuote
  | StartInterp
  | EndInterp

export
Show Kind where
  show Ident   = "Ident"
  show UIdent   = "UIdent"
  show Keyword = "Keyword"
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
  show JSLit = "JSLit"
  show Projection = "Projection"
  show StartQuote = "StartQuote"
  show EndQuote = "EndQuote"
  show StartInterp = "StartInterp"
  show EndInterp = "EndInterp"

export
Eq Kind where
  a == b = show a == show b

public export
record Token where
  constructor Tok
  kind : Kind
  text : String


export
Show Token where
  show (Tok k v) = "<\{show k}:\{show v}>"

public export
BTok : Type
BTok = WithBounds Token

export
value : BTok -> String
value (MkBounded (Tok _ s) _) = s

export
kind : BTok -> Kind
kind (MkBounded (Tok k s) _) = k

export
start : BTok -> (Int, Int)
start (MkBounded _ (MkBounds l c _ _)) = (l,c)

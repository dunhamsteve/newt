module Lib.Lexer2

data UToken
  = Ident String
  | Let
  | In
  | Data
  | Where
  | Forall
  | Case
  | Of
  | Underscore
  | Operator String
  | Equals
  | Dot
  | Colon
  | Pipe
  | RightArrow
  | FatArrow
  | Number Int
  | Lambda
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | Error

-- we can skip this if we keep the text...

Show UToken where
  show = \case
    Ident name => name
    Let => "let"
    In => "in"
    Data => "data"
    Where => "where"
    Forall => "forall"
    Case => "case"
    Of => "of"
    Underscore => "_"
    Operator name => name
    Equals => ?rhs_10
    Dot => ?rhs_11
    Colon => ?rhs_12
    Pipe => ?rhs_13
    RightArrow => ?rhs_14
    FatArrow => ?rhs_15
    Number i => show i
    Lambda => ?rhs_17
    LeftParen => ?rhs_18
    RightParen => ?rhs_19
    LeftBrace => ?rhs_20
    RightBrace => ?rhs_21
    Error => ?rhs_22



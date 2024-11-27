module Lib.Parser.Impl

import Lib.Token
import Lib.Common
import Data.String
import Data.Nat
import Data.List1

public export
TokenList : Type
TokenList = List BTok

-- Result of a parse
public export
data Result : Type -> Type where
  OK : a -> (toks : TokenList) -> (com : Bool) -> Operators -> Result a
  Fail : Bool -> Error -> (toks : TokenList) -> (com : Bool) -> Operators -> Result a

export
Functor Result where
  map f (OK a toks com ops) = OK (f a) toks com ops
  map _ (Fail fatal err toks com ops) = Fail fatal err toks com ops

-- So sixty just has a newtype function here now (probably for perf).
-- A record might be more ergonomic, but would require a record impl before
-- self hosting.

-- FC is a line and column for indents. The idea being that we check
-- either the col < tokCol or line == tokLine, enabling sameLevel.

-- We need State for operators (or postpone that to elaboration)
-- Since I've already built out the pratt stuff, I guess I'll
-- leave it in the parser for now

-- This is a Reader in FC, a State in Operators, Commit flag, TokenList

export
data Parser a = P (TokenList -> Bool -> Operators -> (lc : FC) -> Result a)

export
runP : Parser a -> TokenList -> Bool -> Operators -> FC -> Result a
runP (P f) = f

-- FIXME no filename, also half the time it is pointing at the token after the error
error : String -> TokenList -> String -> Error
error fn [] msg = E (MkFC fn (0,0)) msg
error fn ((MkBounded val isIrrelevant (MkBounds line col _ _)) :: _) msg = E (MkFC fn (line,col)) msg

export
parse : String -> Parser a -> TokenList -> Either Error a
parse fn pa toks = case runP pa toks False empty (MkFC fn (-1,-1)) of
  Fail fatal err toks com ops => Left err
  OK a [] _ _ => Right a
  OK a ts _ _ => Left (error fn ts "Extra toks")

||| Intended for parsing a top level declaration
export
partialParse : String -> Parser a -> Operators -> TokenList -> Either Error (a, Operators, TokenList)
partialParse fn pa ops toks = case runP pa toks False ops (MkFC fn (0,0)) of
  Fail fatal err toks com ops => Left err
  OK a ts _ ops => Right (a,ops,ts)

-- I think I want to drop the typeclasses for v1

export
try : Parser a -> Parser a
try (P pa) = P $ \toks,com,ops,col => case pa toks com ops col of
  (Fail x err toks com ops) => Fail x err toks False ops
  res => res

export
fail : String -> Parser a
fail msg = P $ \toks,com,ops,col => Fail False (error col.file toks msg) toks com ops

export
fatal : String -> Parser a
fatal msg = P $ \toks,com,ops,col => Fail True (error col.file toks msg) toks com ops

export
getOps : Parser (Operators)
getOps = P $ \ toks, com, ops, col => OK ops toks com ops

export
addOp : String -> Int -> Fixity -> Parser ()
addOp nm prec fix = P $ \ toks, com, ops, col =>
  let parts = split (=='_') nm in
  case parts of
    "" ::: key :: rule => OK () toks com (insert key (MkOp nm prec fix False rule) ops)
    key ::: rule => OK () toks com (insert key (MkOp nm prec fix True rule) ops)



export
Functor Parser where
  map f (P pa) = P $ \ toks, com, ops, col => map f (pa toks com ops col)

export
Applicative Parser where
  pure pa = P (\ toks, com, ops, col => OK pa toks com ops)
  P pab <*> P pa = P $ \toks,com,ops,col =>
    case pab toks com ops col of
      Fail fatal err toks com ops => Fail fatal err toks com ops
      OK f toks com ops =>
        case pa toks com ops col of
          (OK x toks com ops) => OK (f x) toks com ops
          (Fail fatal err toks com ops) => Fail fatal err toks com ops

-- Second argument lazy so we don't have circular refs when defining parsers.
export
(<|>) : Parser a -> Lazy (Parser a) -> Parser a
(P pa) <|> (P pb) = P $ \toks,com,ops,col =>
  case pa toks False ops col of
    OK a toks' _ ops => OK a toks' com ops
    Fail True  err toks' com ops  => Fail True err toks' com ops
    Fail fatal err toks' True ops => Fail fatal err toks' True ops
    Fail fatal err toks' False ops => pb toks com ops col

export
Monad Parser where
  P pa >>= pab = P $ \toks,com,ops,col =>
    case pa toks com ops col of
      (OK a toks com ops) => runP (pab a) toks com ops col
      (Fail fatal err xs x ops) => Fail fatal err xs x ops


pred : (BTok -> Bool) -> String -> Parser String
pred f msg = P $ \toks,com,ops,col =>
  case toks of
    (t :: ts) => if f t then OK (value t) ts True ops else Fail False (error col.file toks "\{msg} at \{show $ kind t}:\{value t}") toks com ops
    [] => Fail False (error col.file toks "\{msg} at EOF") toks com ops

export
commit : Parser ()
commit = P $ \toks,com,ops,col => OK () toks True ops

mutual
  export some : Parser a -> Parser (List a)
  some p = (::) <$> p <*> many p

  export many : Parser a -> Parser (List a)
  many p = some p <|> pure []

export
getPos : Parser FC
getPos = P $ \toks, com, ops, indent => case toks of
  [] => OK emptyFC toks com ops
  (t :: ts) => OK (MkFC indent.file (start t)) toks com ops

||| Start an indented block and run parser in it
export
startBlock : Parser a -> Parser a
startBlock (P p) = P $ \toks,com,ops,indent => case toks of
  [] => p toks com ops indent
  (t :: _) =>
    -- If next token is at or before the current level, we've got an empty block
    let (tl,tc) = start t
        (MkFC file (line,col)) = indent
    in p toks com ops (MkFC file (tl, ifThenElse (tc <= col) (col + 1) tc))

||| Assert that parser starts at our current column by
||| checking column and then updating line to match the current
export
sameLevel : Parser a -> Parser a
sameLevel (P p) = P $ \toks,com,ops,indent => case toks of
  [] => p toks com ops indent
  (t :: _) =>
    let (tl,tc) = start t
        (MkFC file (line,col)) = indent
    in if tc == col then p toks com ops ({start := (tl, col)} indent)
    else if col < tc then Fail False (error file toks "unexpected indent") toks com ops
    else Fail False (error file toks "unexpected indent") toks com ops

export
someSame : Parser a -> Parser (List a)
someSame pa = some $ sameLevel pa

export
manySame : Parser a -> Parser (List a)
manySame pa = many $ sameLevel pa

||| check indent on next token and run parser
export
indented : Parser a -> Parser a
indented (P p) = P $ \toks,com,ops,indent => case toks of
  [] => p toks com ops indent
  (t::_) =>
    let (tl,tc) = start t
    in if tc > indent.col || tl == indent.line then p toks com ops indent
    else Fail False (error indent.file toks "unexpected outdent") toks com ops

||| expect token of given kind
export
token' : Kind -> Parser String
token' k = pred (\t => t.val.kind == k) "Expected a \{show k} token"

export
keyword' : String -> Parser ()
keyword' kw = ignore $ pred (\t => t.val.text == kw) "Expected \{kw}"

||| expect indented token of given kind
export
token : Kind -> Parser String
token = indented . token'

export
keyword : String -> Parser ()
keyword kw = indented $ keyword' kw

export
sym : String -> Parser ()
sym = keyword


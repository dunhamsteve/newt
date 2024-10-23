module Lib.Parser.Impl

import Lib.Token
import Data.String
import Data.Nat

public export
TokenList : Type
TokenList = List BTok

public export
data Fixity = InfixL | InfixR | Infix

export
Show Fixity where
  show InfixL = "infixl"
  show InfixR = "infixr"
  show Infix = "infix"

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
data Error = E FC String
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

public export
record OpDef where
  constructor MkOp
  name : String
  prec : Int
  fix : Fixity

-- Result of a parse
public export
data Result : Type -> Type where
  OK : a -> (toks : TokenList) -> (com : Bool) -> List OpDef -> Result a
  Fail : Bool -> Error -> (toks : TokenList) -> (com : Bool) -> List OpDef -> Result a

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
data Parser a = P (TokenList -> Bool -> List OpDef -> (lc : FC) -> Result a)

export
runP : Parser a -> TokenList -> Bool -> List OpDef -> FC -> Result a
runP (P f) = f

error : TokenList -> String -> Error
error [] msg = E emptyFC msg
error ((MkBounded val isIrrelevant (MkBounds line col _ _)) :: _) msg = E (line, col) msg

export
parse : Parser a -> TokenList -> Either Error a
parse pa toks = case runP pa toks False [] (-1,-1) of
  Fail fatal err toks com ops => Left err
  OK a [] _ _ => Right a
  OK a ts _ _ => Left (error ts "Extra toks")

||| Intended for parsing a top level declaration
export
partialParse : Parser a -> List OpDef -> TokenList -> Either Error (a, List OpDef, TokenList)
partialParse pa ops toks = case runP pa toks False ops (0,0) of
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
fail msg = P $ \toks,com,ops,col => Fail False (error toks msg) toks com ops

export
fatal : String -> Parser a
fatal msg = P $ \toks,com,ops,col => Fail True (error toks msg) toks com ops

export
getOps : Parser (List OpDef)
getOps = P $ \ toks, com, ops, col => OK ops toks com ops

export
addOp : String -> Int -> Fixity -> Parser ()
addOp nm prec fix = P $ \ toks, com, ops, col =>
  OK () toks com ((MkOp nm prec fix) :: ops)

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
    (t :: ts) => if f t then OK (value t) ts True ops else Fail False (error toks "\{msg} at \{show $ kind t}:\{value t}") toks com ops
    [] => Fail False (error toks "\{msg} at EOF") toks com ops

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
getPos = P $ \toks,com, ops, (l,c) => case toks of
  [] => OK emptyFC toks com ops
  (t :: ts) => OK (start t) toks com ops

||| Start an indented block and run parser in it
export
startBlock : Parser a -> Parser a
startBlock (P p) = P $ \toks,com,ops,(l,c) => case toks of
  [] => p toks com ops (l,c)
  (t :: _) =>
    -- If next token is at or before the current level, we've got an empty block
    let (tl,tc) = start t
    in p toks com ops (tl,ifThenElse (tc <= c) (c + 1) tc)

||| Assert that parser starts at our current column by
||| checking column and then updating line to match the current
export
sameLevel : Parser a -> Parser a
sameLevel (P p) = P $ \toks,com,ops,(l,c) => case toks of
  [] => p toks com ops (l,c)
  (t :: _) =>
    let (tl,tc) = start t
    in if tc == c then p toks com ops (tl, c)
    else if c < tc then Fail False (error toks "unexpected indent") toks com ops
    else Fail False (error toks "unexpected indent") toks com ops

export
someSame : Parser a -> Parser (List a)
someSame pa = some $ sameLevel pa

export
manySame : Parser a -> Parser (List a)
manySame pa = many $ sameLevel pa

||| check indent on next token and run parser
export
indented : Parser a -> Parser a
indented (P p) = P $ \toks,com,ops,(l,c) => case toks of
  [] => p toks com ops (l,c)
  (t::_) =>
    let (tl,tc) = start t
    in if tc > c || tl == l then p toks com ops (l,c)
    else Fail False (error toks "unexpected outdent") toks com ops

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


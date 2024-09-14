module Lib.Parser.Impl

-- For some reason I'm doing Idris' commit / mustWork dance here, even though it
-- seems to be painful

-- Probably would like to do "did consume anything" on the input, but we might need
-- something other than a token list

-- TODO see what Kovacs' flatparse does for error handling / <|>

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

-- Result of a parse
public export
data Result : Type -> Type where
  OK : a -> (toks : TokenList) -> (com : Bool) -> List (String, Int, Fixity) -> Result a
  Fail : Bool -> Error -> (toks : TokenList) -> (com : Bool) -> List (String, Int, Fixity) -> Result a

export
Functor Result where
  map f (OK a toks com ops) = OK (f a) toks com ops
  map _ (Fail fatal err toks com ops) = Fail fatal err toks com ops

-- So sixty just has a newtype function here now (probably for perf).
-- A record might be more ergonomic, but would require a record impl before
-- self hosting.

-- FC is a line and column for indents. The idea being that we check
-- either the col < tokCol or line == tokLine, enabling sameLevel.

-- This is a Reader in FC

-- we need State for operators (or postpone that to elaboration)
-- Since I've already built out the pratt stuff, I guess I'll
-- leave it in the parser for now

export
data Parser a = P (TokenList -> Bool -> List (String, Int, Fixity) -> (lc : FC) -> Result a)

export
runP : Parser a -> TokenList -> Bool -> List (String, Int, Fixity) -> FC -> Result a
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

-- I think I want to drop the typeclasses for v1

export
fail : String -> Parser a
fail msg = P $ \toks,com,ops,col => Fail False (error toks msg) toks com ops

export
fatal : String -> Parser a
fatal msg = P $ \toks,com,ops,col => Fail True (error toks msg) toks com ops

-- mustWork / commit copied from Idris, but I may switch to the parsec consumption thing.
export
mustWork : Parser a -> Parser a
mustWork (P pa) = P $ \ toks, com, ops, col => case (pa toks com ops col) of
    Fail x err xs y ops => Fail True err xs y ops
    res => res

export
getOps : Parser (List (String, Int, Fixity))
getOps = P $ \ toks, com, ops, col => OK ops toks com ops

export
addOp : String -> Int -> Fixity -> Parser ()
addOp nm prec fix = P $ \ toks, com, ops, col =>
  OK () toks com ((nm, prec, fix) :: ops)

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

-- REVIEW it would be nice if the second argument was lazy...
export
(<|>) : Parser a -> Lazy (Parser a) -> Parser a
(P pa) <|> (P pb) = P $ \toks,com,ops,col =>
  case pa toks False ops col of
    OK a toks' _ ops => OK a toks' com ops
    Fail True  err toks' com ops  => Fail True err toks' com ops
    Fail fatal err toks' True ops => Fail fatal err toks' com ops
    Fail fatal err toks' False ops => pb toks com ops col

export
Monad Parser where
  P pa >>= pab = P $ \toks,com,ops,col =>
    case pa toks com ops col of
      (OK a toks com ops) => runP (pab a) toks com ops col
      (Fail fatal err xs x ops) => Fail fatal err xs x ops


-- do we need this?
pred : (BTok -> Bool) -> String -> Parser String
pred f msg = P $ \toks,com,ops,col =>
  case toks of
    (t :: ts) => if f t then OK (value t) ts com ops else Fail False (error toks "\{msg} at \{show $ kind t}:\{value t}") toks com ops
    [] => Fail False (error toks "\{msg} at EOF") toks com ops

export
commit : Parser ()
commit = P $ \toks,com,ops,col => OK () toks True ops

mutual
  export some : Parser a -> Parser (List a)
  some p = (::) <$> p <*> many p

  export many : Parser a -> Parser (List a)
  many p = some p <|> pure []

-- sixty let has some weird CPS stuff, but essentially:

-- case token_ of
--   Lexer.LLet -> PLet <$> blockOfMany let_ <* token Lexer.In <*> term

-- withIndentationBlock - sets the col
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

||| requires a token to be indented?
export
indented : Parser a -> Parser a
indented (P p) = P $ \toks,com,ops,(l,c) => case toks of
  [] => p toks com ops (l,c)
  (t::_) =>
    let (tl,tc) = start t
    in if tc > c || tl == l then p toks com ops (l,c)
    else Fail False (error toks "unexpected outdent") toks com ops

export
token' : Kind -> Parser String
token' k = pred (\t => t.val.kind == k) "Expected a \{show k} token"

export
keyword' : String -> Parser ()
keyword' kw = ignore $ pred (\t => t.val.text == kw) "Expected \{kw}"

export
token : Kind -> Parser String
token = indented . token'

export
keyword : String -> Parser ()
keyword kw = indented $ keyword' kw

export
sym : String -> Parser ()
sym = keyword


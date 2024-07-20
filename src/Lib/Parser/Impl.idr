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

-- I was going to use a record, but we're peeling this off of bounds at the moment.
public export
SourcePos : Type
SourcePos = (Int,Int)

emptyPos : SourcePos
emptyPos = (0,0)

-- Error of a parse
public export
data Error = E SourcePos String
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
  OK : a -> (toks : TokenList) -> (com : Bool) -> Result a
  Fail : Bool -> Error -> (toks : TokenList) -> (com : Bool)  -> Result a

export
Functor Result where
  map f (OK a toks com ) = OK (f a) toks com
  map _ (Fail fatal err toks com) = Fail fatal err toks com

-- So sixty just has a newtype function here now (probably for perf).
-- A record might be more ergonomic, but would require a record impl before
-- self hosting.

-- We keep the line and column for indents. The idea being that we check
-- either the col < tokCol or line == tokLine, enabling sameLevel.

-- dunno why I'm making that a pair..
export
data Parser a = P (TokenList -> Bool -> (lc : SourcePos) -> Result a)

export
runP : Parser a -> TokenList -> Bool -> SourcePos -> Result a
runP (P f) = f

error : TokenList -> String -> Error
error [] msg = E emptyPos msg
error ((MkBounded val isIrrelevant (MkBounds line col _ _)) :: _) msg = E (line, col) msg

export
parse : Parser a -> TokenList -> Either Error a
parse pa toks = case runP pa toks False emptyPos of
  Fail fatal err toks com => Left err
  OK a [] _ => Right a
  OK a ts _ => Left (error ts "Extra toks")

-- I think I want to drop the typeclasses for v1

export
fail : String -> Parser a
fail msg = P $ \toks,com,col => Fail False (error toks msg) toks com

export
fatal : String -> Parser a
fatal msg = P $ \toks,com,col => Fail False (error toks msg) toks com

-- mustWork / commit copied from Idris, but I may switch to the parsec consumption thing.
export
mustWork : Parser a -> Parser a
mustWork (P pa) = P $ \ toks, com, col => case (pa toks com col) of
    Fail x err xs y => Fail True err xs y
    res => res

export
Functor Parser where
  map f (P pa) = P $ \ toks, com, col => map f (pa toks com col)

export
Applicative Parser where
  pure pa = P (\ toks, com, col => OK pa toks com)
  P pab <*> P pa = P $ \toks,com,col =>
    case pab toks com col of
      Fail fatal err toks com => Fail fatal err toks com
      OK f toks com =>
        case pa toks com col of
          (OK x toks com) => OK (f x) toks com
          (Fail fatal err toks com) => Fail fatal err toks com

-- REVIEW it would be nice if the second argument was lazy...
export
(<|>) : Parser a -> Lazy (Parser a) -> Parser a
(P pa) <|> (P pb) = P $ \toks,com,col =>
  case pa toks False col of
    OK a toks' _ => OK a toks' com
    Fail True  err toks' com   => Fail True err toks' com
    Fail fatal err toks' True  => Fail fatal err toks' com
    Fail fatal err toks' False => pb toks com col

export
Monad Parser where
  P pa >>= pab = P $ \toks,com,col =>
    case pa toks com col of
      (OK a toks com) => runP (pab a) toks com col
      (Fail fatal err xs x) => Fail fatal err xs x


-- do we need this?
pred : (BTok -> Bool) -> String -> Parser String
pred f msg = P $ \toks,com,col =>
  case toks of
    (t :: ts) => if f t then OK (value t) ts com else Fail False (error toks "\{msg} vt:\{value t}") toks com
    [] => Fail False (error toks "\{msg} at EOF") toks com

export
commit : Parser ()
commit = P $ \toks,com,col => OK () toks True

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
getPos : Parser SourcePos
getPos = P $ \toks,com, (l,c) => case toks of
  [] => Fail False (error toks "End of file") toks com -- OK emptyPos toks com
  (t :: ts) => OK (start t) toks com

||| Start an indented block and run parser in it
export
startBlock : Parser a -> Parser a
startBlock (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t :: _) =>
    let (tl,tc) = start t
    in p toks com (tl,tc)

||| Assert that parser starts at our current column by
||| checking column and then updating line to match the current
export
sameLevel : Parser a -> Parser a
sameLevel (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t :: _) =>
    let (tl,tc) = start t
    in if tc == c then p toks com (tl, c)
    else if c < tc then Fail False (error toks "unexpected indent") toks com
    else Fail False (error toks "unexpected indent") toks com

export
someSame : Parser a -> Parser (List a)
someSame pa = some $ sameLevel pa

export
manySame : Parser a -> Parser (List a)
manySame pa = many $ sameLevel pa

||| requires a token to be indented?
export
indented : Parser a -> Parser a
indented (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t::_) =>
    let (tl,tc) = start t
    in if tc > c || tl == l then p toks com (l,c)
    else Fail False (error toks "unexpected outdent") toks com

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


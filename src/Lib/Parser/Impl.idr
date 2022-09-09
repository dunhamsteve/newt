module Lib.Parser.Impl

import Lib.Token

public export
TokenList : Type
TokenList = List BTok

-- Error of a parse
public export
data Error = E String
%name Error err

-- Result of a parse
public export
data Result : Type -> Type where
  OK : a -> (toks : TokenList) -> (com : Bool) -> Result a
  Fail : Error -> (toks : TokenList) -> (com : Bool)  -> Result a  

export
Functor Result where
  map f (OK a toks com ) = OK (f a) toks com
  map _ (Fail err toks com) = Fail err toks com

-- So sixty just has a newtype function here now (probably for perf).
-- A record might be more ergonomic, but would require a record impl before
-- self hosting.

-- We keep the line and column for indents. The idea being that we check
-- either the col < tokCol or line == tokLine, enabling sameLevel.

-- dunno why I'm making that a pair..
export
data Parser a = P (TokenList -> Bool -> (lc : (Int,Int)) -> Result a)

runP : Parser a -> TokenList -> Bool -> (Int,Int) -> Result a
runP (P f) = f

fail : String -> Parser a
fail msg = P $ \toks,com,col => Fail (E msg) toks com

export
Functor Parser where
  map f (P pa) = P $ \ toks, com, col => map f (pa toks com col)

export
Applicative Parser where 
  pure pa = P (\ toks, com, col => OK pa toks com)
  P pab <*> P pa = P $ \toks,com,col =>
    case pab toks com col of
      Fail err toks com => Fail err toks com
      OK f toks com => 
        case pa toks com col of 
          (OK x toks com) => OK (f x) toks com
          (Fail err toks com) => Fail err toks com

export
Alternative Parser where
  empty = fail "empty"
  (P pa) <|> (P pb) = P $ \toks,com,col =>
    case pa toks com col of
      f@(Fail _ _ com') => if com' then f else pb toks com col
      t => t

export
Monad Parser where
  P pa >>= pab = P $ \toks,com,col =>
    case pa toks com col of
      (OK a toks com) => runP (pab a) toks com col
      (Fail err xs x) => ?rhs_1


-- do we need this?
pred : (BTok -> Bool) -> String -> Parser String
pred f msg = P $ \toks,com,col =>
  case toks of
    (t :: ts) => if f t then OK (value t) ts com else Fail (E msg) toks com
    [] => Fail (E "eof") toks com

export
commit : Parser ()
commit = P $ \toks,com,col => OK () toks True

export
token : Kind -> Parser String
token k = pred (\t => t.val.kind == k) "Expected a \{show k}"


export
keyword : String -> Parser ()
keyword kw = ignore $ pred (\t => t.val.text == kw) "Expected \{kw}"


many : Parser a -> Parser (List a)
some : Parser a -> Parser (List a)
some p = (::) <$> p <*> many p
many p = some p <|> pure []

-- sixty let has some weird CPS stuff, but essentially:

-- case token_ of
--   Lexer.LLet -> PLet <$> blockOfMany let_ <* token Lexer.In <*> term

-- withIndentationBlock - sets the col

||| Start an indented block and run parser in it
export
startBlock : Parser a -> Parser a
startBlock (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t :: ts) =>
    let (tl,tc) = start t
    in p toks com (tl,tc)

||| Assert that parser starts at our current column by
||| checking column and then updating line to match the current
export
sameLevel : Parser a -> Parser a
sameLevel (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t :: ts) => 
    let (tl,tc) = start t 
    in if tc == c then p toks com (tl, c)
    else if c < tc then Fail (E "unexpected indent") toks com
    else Fail (E "unexpected indent") toks com

export
someSame : Parser a -> Parser (List a)
someSame = some . sameLevel

||| requires a token to be indented?
indented : Parser a -> Parser a
indented (P p) = P $ \toks,com,(l,c) => case toks of
  [] => p toks com (l,c)
  (t::ts) =>
    let (tl,tc) = start t
    in if tc > c || tl == l then p toks com (l,c)
    else Fail (E "unexpected outdent") toks com


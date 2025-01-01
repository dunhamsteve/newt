module Lib.Tokenizer

-- Working alternate tokenizer, saves about 2k, can be translated to newt

-- Currently this processes a stream of characters, I may switch it to
-- combinators for readability in the future.

import Lib.Token
import Lib.Common
import Data.String

standalone : List Char
standalone = unpack "()\\{}[],.@"

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data", "U", "do",
            "ptype", "pfunc", "module", "infixl", "infixr", "infix",
            "∀", "forall", "import", "uses",
            "class", "instance", "record", "constructor",
            "if", "then", "else",
            -- it would be nice to find a way to unkeyword "." so it could be
            -- used as an operator too
            "$", "λ", "?", "@", ".",
             "->", "→", ":", "=>", ":=", "=", "<-", "\\", "_", "|"]

record TState where
  constructor TS
  trow : Int
  tcol : Int
  acc : SnocList BTok
  chars : List Char

-- This makes a big case tree...
rawTokenise : TState -> Either Error TState

quoteTokenise : TState -> Int -> Int -> SnocList Char -> Either Error TState
quoteTokenise ts@(TS el ec toks chars) sl sc acc = case chars of
  '"' :: cs => Right (TS el ec (toks :< stok) chars)
  '\\' :: '{' :: cs => do
    let tok = MkBounded (Tok StartInterp "\\{") (MkBounds el ec el (ec + 2))
    (TS sl sc toks chars) <- rawTokenise $ TS el (ec + 2) (toks :< stok :< tok) cs
    case chars of
      '}' :: cs =>
        let tok = MkBounded (Tok EndInterp "}") (MkBounds el ec el (ec + 1))
        in quoteTokenise (TS el (ec + 1) (toks :< tok) cs) el (ec + 1) [<]
      cs => Left $ E (MkFC "" (el, ec)) "Expected '{'"
  -- TODO newline in string should be an error
  '\\' :: 'n' :: cs => quoteTokenise (TS el (ec + 2) toks cs) sl sc (acc :< '\n')
  '\\' :: c :: cs => quoteTokenise (TS el (ec + 2) toks cs) sl sc (acc :< c)
  c :: cs => quoteTokenise (TS el (ec + 1) toks cs) sl sc (acc :< c)
  Nil => Left $ E (MkFC "" (el, ec)) "Expected '\"' at EOF"

  where
    stok : BTok
    stok = MkBounded (Tok StringKind (pack $ acc <>> [])) (MkBounds sl sc el ec)



rawTokenise ts@(TS sl sc toks chars) = case chars of
  Nil => Right $ ts
  ' ' :: cs => rawTokenise (TS sl (sc + 1) toks cs)
  '\n' :: cs => rawTokenise (TS (sl + 1) 0 toks cs)
  '{' :: '{' :: cs => rawTokenise (TS sl (sc + 2) (toks :< mktok False sl (sc + 2) Keyword "{{" ) cs)
  '}' :: '}' :: cs => rawTokenise (TS sl (sc + 2) (toks :< mktok False sl (sc + 2) Keyword "}}" ) cs)

  '"' :: cs => do
    let tok = mktok False sl (sc + 1) StartQuote "\""
    (TS sl sc toks chars) <- quoteTokenise (TS sl (sc + 1) (toks :< tok) cs) sl (sc + 1) [<]
    case chars of
      '"' :: cs => let tok = mktok False sl (sc + 1) EndQuote "\"" in
        rawTokenise (TS sl (sc + 1) (toks :< tok) cs)
      cs => Left $ E (MkFC "" (sl, sc)) "Expected '\"'"


  '}' :: cs => Right ts
  '{' :: cs => do
    let tok = mktok False sl (sc + 1) Symbol "{"
    (TS sl sc toks chars) <- rawTokenise (TS sl (sc + 1) (toks :< tok) cs)
    case chars of
      '}' :: cs => let tok = mktok False sl (sc + 1) Symbol "}" in
        rawTokenise (TS sl (sc + 1) (toks :< tok) cs)
      cs => Left $ E (MkFC "" (sl, sc)) "Expected '}'"

  ',' :: cs => rawTokenise (TS sl (sc + 1) (toks :< mktok False sl (sc + 1) Ident ",") cs)
  '_' :: ',' :: '_' :: cs => rawTokenise (TS sl (sc + 3) (toks :< mktok False sl (sc + 3) MixFix "_,_") cs)
  '_' :: '.' :: '_' :: cs => rawTokenise (TS sl (sc + 3) (toks :< mktok False sl (sc + 3) MixFix "_._") cs)
  '\'' :: '\\' :: c :: '\'' :: cs =>
    let ch = ifThenElse (c == 'n') '\n' c
    in rawTokenise (TS sl (sc + 4) (toks :< mktok False sl (sc + 4) Character (singleton ch)) cs)
  '\'' :: c :: '\'' :: cs => rawTokenise (TS sl (sc + 3) (toks :< mktok False sl (sc + 3) Character (singleton c)) cs)
  '#' :: cs => ?do_pragma -- we probably want to require at least one alpha?
  '-' :: '-' :: cs => lineComment (TS sl (sc + 2) toks cs)
  '/' :: '-' :: cs => blockComment (TS sl (sc + 2) toks cs)
  '`' :: cs => doBacktick (TS sl (sc + 1) toks cs) [<]
  '"' :: cs => doQuote (TS sl (sc + 1) toks cs) [<]
  '.' :: cs => doRest (TS sl (sc + 1) toks cs) Projection isIdent (Lin :< '.')
  '-' :: c :: cs => if isDigit c
    then doRest (TS sl (sc + 2) toks cs) Number isDigit (Lin :< '-' :< c)
    else doRest (TS sl (sc + 1) toks (c :: cs)) Ident isIdent (Lin :< '-')

  c :: cs => doChar c cs

  where
    isIdent : Char -> Bool
    isIdent c = not (isSpace c || elem c standalone)

    isUIdent : Char -> Bool
    isUIdent c = isIdent c || c == '.'

    doBacktick : TState -> SnocList Char -> Either Error TState
    doBacktick (TS l c toks Nil) acc = Left $ E (MkFC "" (l,c)) "EOF in backtick string"
    doBacktick (TS el ec toks ('`' :: cs)) acc =
      let tok = MkBounded (Tok JSLit (pack $ acc <>> [])) (MkBounds sl sc el ec) in
      rawTokenise (TS el (ec + 1) (toks :< tok) cs)
    doBacktick (TS l c toks ('\n' :: cs)) acc = doBacktick (TS (l + 1) 0 toks cs) (acc :< '\n')
    doBacktick (TS l c toks (ch :: cs)) acc = doBacktick (TS l (c + 1) toks cs) (acc :< ch)


    -- temporary use same token as before
    mktok : Bool -> Int -> Int -> Kind -> String -> BTok
    mktok checkkw el ec kind text = let kind = if checkkw && elem text keywords then Keyword else kind in
      MkBounded (Tok kind text) (MkBounds sl sc el ec)

    lineComment : TState -> Either Error TState
    lineComment (TS line col toks Nil) = rawTokenise (TS line col toks Nil)
    lineComment (TS line col toks ('\n' :: cs)) = rawTokenise (TS (line + 1) 0 toks cs)
    lineComment (TS line col toks (c :: cs)) = lineComment (TS line (col + 1) toks cs)

    blockComment : TState -> Either Error TState
    blockComment (TS line col toks Nil) = Left $ E (MkFC "" (line, col)) "EOF in block comment"
    blockComment (TS line col toks ('-' :: '/' :: cs)) = rawTokenise (TS line (col + 2) toks cs)
    blockComment (TS line col toks ('\n' :: cs)) = blockComment (TS (line + 1) 0 toks cs)
    blockComment (TS line col toks (c :: cs)) = blockComment (TS line (col + 1) toks cs)

    doRest : TState -> Kind -> (Char -> Bool) -> SnocList Char -> Either Error TState
    doRest (TS l c toks Nil) kind pred acc = rawTokenise (TS l c (toks :< mktok True l c kind (pack $ acc <>> [])) Nil)
    doRest (TS l c toks (ch :: cs)) kind pred acc = if pred ch
      then doRest (TS l (c + 1) toks cs) kind pred (acc :< ch)
      else
        let kind = if elem '_' acc then MixFix else kind in
        rawTokenise (TS l c (toks :< mktok True l (c - 1) kind (pack $ acc <>> [])) (ch :: cs))

    doQuote : TState -> SnocList Char -> Either Error TState
    -- should be an error..
    doQuote (TS line col toks Nil) acc = ?missing_end_quote
    doQuote (TS line col toks ('\\' :: 'n' :: cs)) acc = doQuote (TS line (col + 2) toks cs) (acc :< '\n')
    doQuote (TS line col toks ('\\' :: c :: cs)) acc = doQuote (TS line (col + 2) toks cs) (acc :< c)
    doQuote (TS line col toks ('\n' :: cs)) acc = ?error_newline_in_quote
    doQuote (TS line col toks ('"' :: cs)) acc = rawTokenise (TS line (col + 1) (toks :< mktok False line (col + 1) StringKind (pack $ acc <>> [])) cs)
    doQuote (TS line col toks (c :: cs)) acc = doQuote (TS line (col + 1) toks cs) (acc :< c)

    doChar : Char -> List Char ->  Either Error TState
    doChar c cs = if elem c standalone
      then rawTokenise (TS sl (sc + 1) (toks :< mktok True sl (sc + 1) Symbol (singleton c)) cs)
      else let kind = if isDigit c then Number else if isUpper c then UIdent else Ident in
        doRest (TS sl sc toks (c :: cs)) kind isIdent [<]

export
tokenise : String -> String -> Either Error (List BTok)
tokenise fn text = case rawTokenise (TS 0 0 Lin (unpack text)) of
  Right (TS trow tcol acc []) => Right $ acc <>> []
  Right (TS trow tcol acc chars) => Left $ E (MkFC fn (trow, tcol)) "Extra toks"
  Left (E (MkFC file start) str) => Left $ E (MkFC fn start) str
  Left err => Left err


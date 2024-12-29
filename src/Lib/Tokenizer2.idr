module Lib.Tokenizer2

-- Working alternate tokenizer, saves about 2k, can be translated to newt

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
            "$", "λ", "?", "@",
             "->", "→", ":", "=>", ":=", "=", "<-", "\\", "_", "|"]

-- This makes a big case tree...
tokenise' : Int -> Int ->  SnocList BTok -> List Char -> Either Error (List BTok)
tokenise' sl sc toks chars = case chars of
  Nil => Right $ toks <>> []
  ' ' :: cs => tokenise' sl (sc + 1) toks cs
  '\n' :: cs => tokenise' (sl + 1) 0 toks cs
  '{' :: '{' :: cs => tokenise' sl (sc + 2) (toks :< mktok False sl (sc + 2) Keyword "{{" ) cs
  '}' :: '}' :: cs => tokenise' sl (sc + 2) (toks :< mktok False sl (sc + 2) Keyword "}}" ) cs
  ',' :: cs => tokenise' sl (sc + 1) (toks :< mktok False sl (sc + 1) Ident ",") cs
  '_' :: ',' :: '_' :: cs => tokenise' sl (sc + 3) (toks :< mktok False sl (sc + 3) MixFix "_,_") cs
  '_' :: '.' :: '_' :: cs => tokenise' sl (sc + 3) (toks :< mktok False sl (sc + 3) MixFix "_._") cs
  '\'' :: '\\' :: c :: '\'' :: cs =>
    let ch = ifThenElse (c == 'n') '\n' c
    in tokenise' sl (sc + 4) (toks :< mktok False sl (sc + 4) Character (singleton ch)) cs
  '\'' :: c :: '\'' :: cs => tokenise' sl (sc + 3) (toks :< mktok False sl (sc + 3) Character (singleton c)) cs
  '#' :: cs => ?do_pragma -- we probably want to require at least one alpha?
  '-' :: '-' :: cs => lineComment sl (sc + 2) toks cs
  '/' :: '-' :: cs => blockComment sl (sc + 2) toks cs
  '`' :: cs => doBacktick sl (sc + 1) toks cs [<]
  '"' :: cs => doQuote sl (sc + 1) toks cs [<]
  '-' :: c :: cs => if isDigit c
    then doRest sl (sc + 2) toks cs Number isDigit (Lin :< '-' :< c)
    else doRest sl (sc + 1) toks (c :: cs) Ident isIdent (Lin :< '-')

  c :: cs => doChar c cs

  where
    isIdent : Char -> Bool
    isIdent c = not (isSpace c || elem c standalone)

    doBacktick : Int -> Int -> SnocList BTok -> List Char -> SnocList Char -> Either Error (List BTok)
    doBacktick l c toks Nil acc = Left $ E (MkFC "" (l,c)) "EOF in backtick string"
    doBacktick el ec toks ('`' :: cs) acc =
      let tok = MkBounded (Tok JSLit (pack $ acc <>> [])) False (MkBounds sl sc el ec) in
      tokenise' el (ec + 1) (toks :< tok) cs
    doBacktick l c toks ('\n' :: cs) acc = doBacktick (l + 1) 0 toks cs (acc :< '\n')
    doBacktick l c toks (ch :: cs) acc = doBacktick l (c + 1) toks cs (acc :< ch)


    -- temporary use same token as before
    mktok : Bool -> Int -> Int -> Kind -> String -> BTok
    mktok checkkw el ec kind text = let kind = if checkkw && elem text keywords then Keyword else kind in
      MkBounded (Tok kind text) False (MkBounds sl sc el ec)

    lineComment : Int -> Int -> SnocList BTok -> List Char -> Either Error (List BTok)
    lineComment line col toks Nil = tokenise' line col toks Nil
    lineComment line col toks ('\n' :: cs) = tokenise' (line + 1) 0 toks cs
    lineComment line col toks (c :: cs) = lineComment line (col + 1) toks cs

    blockComment : Int -> Int -> SnocList BTok -> List Char -> Either Error (List BTok)
    blockComment line col toks Nil = Left $ E (MkFC "" (line, col)) "EOF in block comment"
    blockComment line col toks ('-' :: '/' :: cs) = tokenise' line (col + 2) toks cs
    blockComment line col toks ('\n' :: cs) = blockComment (line + 1) 0 toks cs
    blockComment line col toks (c :: cs) = blockComment line (col + 1) toks cs


    doRest : Int -> Int -> SnocList BTok -> List Char -> Kind -> (Char -> Bool) -> SnocList Char -> Either Error (List BTok)
    doRest l c toks Nil kind pred acc = tokenise' l c (toks :< mktok True l c kind (pack $ acc <>> [])) Nil
    doRest l c toks (ch :: cs) kind pred acc = if pred ch
      then doRest l (c + 1) toks cs kind pred (acc :< ch)
      else
        let kind = if elem '_' acc then MixFix else kind in
        tokenise' l c (toks :< mktok True l (c - 1) kind (pack $ acc <>> [])) (ch :: cs)

    doQuote : Int -> Int -> SnocList BTok -> List Char -> SnocList Char -> Either Error (List BTok)
    -- should be an error..
    doQuote line col toks Nil acc = ?missing_end_quote
    doQuote line col toks ('\\' :: 'n' :: cs) acc = doQuote line (col + 2) toks cs (acc :< '\n')
    doQuote line col toks ('\\' :: c :: cs) acc = doQuote line (col + 2) toks cs (acc :< c)
    doQuote line col toks ('\n' :: cs) acc = ?error_newline_in_quote
    doQuote line col toks ('"' :: cs) acc = tokenise' line (col + 1) (toks :< mktok False line (col + 1) StringKind (pack $ acc <>> [])) cs
    doQuote line col toks (c :: cs) acc = doQuote line (col + 1) toks cs (acc :< c)

    doChar : Char -> List Char ->  Either Error (List BTok)
    doChar c cs = if elem c standalone
      then tokenise' sl (sc + 1) (toks :< mktok True sl (sc + 1) Symbol (singleton c)) cs
      else let kind = if isDigit c then Number else if isUpper c then UIdent else Ident in
        doRest sl sc toks (c :: cs) kind isIdent [<]

export
tokenise : String -> String -> Either Error (List BTok)
tokenise fn text = case tokenise' 0 0 Lin (unpack text) of
  Left (E (MkFC file start) str) => Left (E (MkFC fn start) str)
  res => res

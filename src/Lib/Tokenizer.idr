module Lib.Tokenizer

import Text.Lexer
import Text.Lexer.Tokenizer
import Lib.Token
import Lib.Common

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data", "U", "do",
            "ptype", "pfunc", "module", "infixl", "infixr", "infix",
            "->", "→", ":", "=>", ":=", "=", "<-", "\\", "_"]

specialOps : List String
specialOps = ["->", ":", "=>", ":=", "=", "<-"]

checkKW : String -> Token Kind
checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

checkUKW : String -> Token Kind
checkUKW s = if elem s keywords then Tok Keyword s else Tok UIdent s

identMore : Lexer
identMore = alphaNum <|> exact "." <|> exact "'" <|> exact "_"

singleton : Lexer
singleton = oneOf "()\\{}[],"

quo : Recognise True
quo = is '"'

esc : Recognise True -> Recognise True
esc l = is '\\' <+> l

-- REVIEW maybe we can do this faster with the view thinger
unquote : String -> String
unquote str = case unpack str of
  ('"' :: xs) => pack $ go xs
  imp => pack $ go imp
  where
    go : List Char -> List Char
    go [] = []
    go ['"'] = []
    go ('\\' :: ('n' :: xs)) = '\n' :: go xs
    go ('\\' :: (x :: xs)) = x :: go xs
    go (x :: xs) = x :: go xs

opMiddle = pred (\c => not (isSpace c || c == '_'))

rawTokens : Tokenizer (Token Kind)
rawTokens
  = match spaces (Tok Space)
  -- { is singleton except for {{
  <|> match (exact "{{" <|> exact "}}") (Tok Keyword)
  -- need to make this an ident
  <|> match (exact ",") (checkKW)
  -- for now, our lambda slash is singleton
  <|> match (singleton) (Tok Symbol)
  -- TODO Drop MixFix token type when we support if_then_else_
  <|> match (exact "_" <+> (some opMiddle) <+> exact "_") (Tok MixFix)
  -- REVIEW - expect non-alpha after?
  <|> match (some digit) (Tok Number)
  -- for module names and maybe type constructors
  <|> match (charLit) (Tok Character)
  <|> match (is '#' <+> many alpha) (Tok Pragma)
  <|> match (lineComment (exact "--")) (Tok Space)
  <|> match (blockComment (exact "/-") (exact "-/")) (Tok Space)
  <|> match (upper <+> many identMore) checkUKW
  <|> match (quo <+> manyUntil quo (esc any <|> any) <+> quo) (Tok StringKind . unquote)
  -- accept almost everything, but
  <|> match (some (non (space <|> singleton))) checkKW

notSpace : WithBounds (Token Kind) -> Bool
notSpace (MkBounded (Tok Space _) _ _) = False
notSpace _ = True

export
tokenise : String -> Either Error (List BTok)
tokenise s = case lex rawTokens s of
  (toks, EndInput, l, c, what) => Right (filter notSpace toks)
  (toks, reason, l, c, what) => Left (E (l,c) "\{show reason}")


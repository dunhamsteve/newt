module Lib.Tokenizer

import Text.Lexer
import Text.Lexer.Tokenizer
import Lib.Token
import Lib.Common

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data", "U", "do",
            "ptype", "pfunc", "module", "infixl", "infixr", "infix",
            "∀", "forall",
            "class", "instance",
            "if", "then", "else",
            "$", "λ",
             "->", "→", ":", "=>", ":=", "=", "<-", "\\", "_", "|"]

checkKW : String -> Token Kind
checkKW s =
  if s /= "_" && elem '_' (unpack s) then Tok MixFix s else
  if elem s keywords then Tok Keyword s
  else Tok Ident s

checkUKW : String -> Token Kind
checkUKW s = if elem s keywords then Tok Keyword s else Tok UIdent s

identMore : Lexer
identMore = alphaNum <|> exact "'" <|> exact "_"

singleton : Lexer
singleton = oneOf "()\\{}[],?."

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

unquoteChar : String -> String
unquoteChar str = pack $ case unpack str of
  ('\'' :: xs) => go xs
  imp => go imp -- shouldn't happen
  where
    go : List Char -> List Char
    go [] = ['\''] -- shouldn't happen
    go ('\\' :: ('n' :: xs)) = ['\n']
    go ('\\' :: (x :: xs)) = [x]
    go (x :: xs) = [x]

opMiddle = pred (\c => not (isSpace c || c == '_'))

btick = is '`'

trimJS : String -> String
trimJS str = case unpack str of
  ('`' :: xs) => pack $ go xs
  bug => pack $ go bug
  where
    go : List Char -> List Char
    go [] = []
    go ['`'] = []
    go (x :: xs) = x :: go xs

%hide charLit
charLit : Lexer
charLit = is '\'' <+> (is '\\' <+> any <|> any) <+> is '\''


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
  <|> match (exact "_,_" <|> exact "_._") (Tok MixFix)
  -- REVIEW - expect non-alpha after?
  <|> match (some digit) (Tok Number)
  -- for module names and maybe type constructors
  <|> match (charLit) (Tok Character . unquoteChar)
  <|> match (is '#' <+> many alpha) (Tok Pragma)
  <|> match (lineComment (exact "--")) (Tok Space)
  <|> match (blockComment (exact "/-") (exact "-/")) (Tok Space)
  <|> match (upper <+> many identMore) checkUKW
  <|> match (btick <+> manyUntil btick any <+> btick) (Tok JSLit . trimJS)
  <|> match (quo <+> manyUntil quo (esc any <|> any) <+> quo) (Tok StringKind . unquote)
  -- accept almost everything, but
  <|> match (some (non (space <|> singleton))) checkKW

notSpace : WithBounds (Token Kind) -> Bool
notSpace (MkBounded (Tok Space _) _ _) = False
notSpace _ = True

export
tokenise : String -> String -> Either Error (List BTok)
tokenise fn s = case lex rawTokens s of
  (toks, EndInput, l, c, what) => Right (filter notSpace toks)
  (toks, reason, l, c, what) => Left (E (MkFC fn (l,c)) "\{show reason}")


module Lib.Tokenizer

import Text.Lexer
import Text.Lexer.Tokenizer
import Lib.Token

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data", "U", "ptype", "pfunc", "module"]

specialOps : List String
specialOps = ["->", ":", "=>", ":="]

checkKW : String -> Token Kind
checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

opChar : Lexer
opChar = pred isOpChar

identMore : Lexer
identMore = alphaNum <|> exact "." <|> exact "'"

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
    go ('\\' :: (x :: xs)) = x :: go xs
    go (x :: xs) = x :: go xs

rawTokens : Tokenizer (Token Kind)
rawTokens
   =  match (alpha <+> many identMore) checkKW
  <|> match (some digit) (Tok Number)
  <|> match (is '#' <+> many alpha) (Tok Pragma)
  <|> match (quo <+> manyUntil quo ((esc any <+> any) <|> any) <+> opt quo) (Tok StringKind . unquote)
  <|> match (lineComment (exact "--")) (Tok Space)
  <|> match (blockComment (exact "/-") (exact "-/")) (Tok Space)
  <|> match (some opChar) (\s => Tok Oper s)
  <|> match symbol (Tok Symbol)
  <|> match spaces (Tok Space)

notSpace : WithBounds (Token Kind) -> Bool
notSpace (MkBounded (Tok Space _) _ _) = False
notSpace _ = True

export
tokenise : String -> List BTok
tokenise = filter notSpace . fst . lex rawTokens

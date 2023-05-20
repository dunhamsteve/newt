module Lib.Tokenizer

import Text.Lexer
import Text.Lexer.Tokenizer
import Lib.Token

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data"]

specialOps : List String
specialOps = ["->", ":", "=>"]

checkKW : String -> Token Kind
checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

opChar : Lexer
opChar = pred isOpChar

identMore : Lexer
identMore = alphaNum <|> exact "."

rawTokens : Tokenizer (Token Kind)
rawTokens
   =  match (alpha <+> many identMore) checkKW
  <|> match (some digit) (Tok Number)
  <|> match (lineComment (exact "--")) (Tok Space)
  <|> match (some opChar) (\s => Tok Oper s)
  <|> match symbol (Tok Symbol)
  <|> match spaces (Tok Space)

notSpace : WithBounds (Token Kind) -> Bool
notSpace (MkBounded (Tok Space _) _ _) = False
notSpace _ = True

export
tokenise : String -> List BTok
tokenise = filter notSpace . fst . lex rawTokens 

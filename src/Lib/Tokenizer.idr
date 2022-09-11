module Lib.Tokenizer

import Text.Lexer
import Text.Lexer.Tokenizer
import Lib.Token

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data"]

specialOps : List String
specialOps = ["->", ":"]

checkKW : String -> Token Kind
checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

opChar : Lexer
opChar = pred isOpChar

-- so Text.Lexer.Core.lex is broken
-- tmap : TokenMap (Token Kind)
-- tmap = [
--   (alpha <+> many alphaNum, checkKW),
--   (some digit, Tok Number),
--   (some opChar, \s => Tok Oper s),
--   (lineComment (exact "--"), Tok Space),
--   (symbol, Tok Symbol),
--   (spaces, Tok Space)
-- ]

rawTokens : Tokenizer (Token Kind)
rawTokens
   =  match (alpha <+> many alphaNum) checkKW
  <|> match (some digit) (Tok Number)
  <|> match (some opChar) (\s => Tok Oper s)
  <|> match (lineComment (exact "--")) (Tok Space)
  <|> match symbol (Tok Symbol)
  <|> match spaces (Tok Space)

notSpace : WithBounds (Token Kind) -> Bool
notSpace (MkBounded (Tok Space _) _ _) = False
notSpace _ = True

export
tokenise : String -> List BTok
tokenise = filter notSpace . fst . lex rawTokens 



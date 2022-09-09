module Lib.Tokenizer2

-- Starting to write from-scratch tokenizer to flatten out the data a little.

data Position = Pos Int Int

inc : Position -> Position
inc (Pos l c) = Pos l (c + 1)


public export
data Kind 
  = Ident 
  | Keyword 
  | Oper 
  | Comment
  | Number 
  | Symbol
  | Arrow
  -- virtual stuff deprecated?
  | LBrace
  | Semi
  | RBrace
  | EOF

data Token = Tok Int Int Kind String

data Lexer
  = Match (Char -> Bool)
  | Seq Lexer 

keywords : List String
keywords = ["let", "in", "where", "case", "of", "data"]

specialOps : List String
specialOps = ["->", ":"]

-- checkKW : String -> Token Kind
-- checkKW s = if elem s keywords then Tok Keyword s else Tok Ident s

opkind : String -> Kind
opkind "->" = Arrow
opkind _    = Oper

isOpChar : Char -> Bool
isOpChar c = c `elem` (unpack ":!#$%&*+./<=>?@\\^|-~")

-- opChar : Lexer
-- opChar = pred isOpChar

token : Int -> Int -> List Char -> (Token, List Char)
token l c cs = case cs of
  [] => (Tok l c EOF "",[])
  ('-' :: '-' :: cs) => scan (/= '\n') ['-','-'] l (c+2) cs
  _ => ?fixme

  where
    scan : (Char -> Bool) -> (List Char) -> Int -> Int -> List Char -> (Token,List Char)


-- match could be a Maybe thing and use the maybe Alt impl.
-- Not sure what shape I want here.  Maybe a straight up Character Parser and drop tokenization.

-- rawTokens : Tokenizer (Token Kind)
-- rawTokens
--    =  match (alpha <+> many alphaNum) checkKW
--   <|> match (some digit) (Tok Number)
--   <|> match (some opChar) (\s => Tok (opkind s) s)
--   <|> match (lineComment (exact "--")) (Tok Space)
--   <|> match symbol (Tok Symbol)
--   <|> match spaces (Tok Space)


-- export
-- tokenise : String -> List BTok
-- tokenise = filter notSpace . fst . lex rawTokens 



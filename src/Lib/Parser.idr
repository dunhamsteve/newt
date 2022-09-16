module Lib.Parser


import Lib.Token
import Lib.Parser.Impl
import Syntax
import Data.List

-- There is the whole core vs surface thing here.
-- might be best to do core first/ Technically don't
-- _need_ a parser, but would be useful for testing.

-- look to pi-forall / ezoo, but I think we start with a
-- TTImpl level grammar, then add a more sugared layer above
-- so holes and all that

-- After the parser runs, see below, take a break and finish pi-forall
-- exercises.  There is some fill in the parser stuff that may show 
-- the future.

ident = token Ident


parens : Parser a -> Parser a
parens pa = do
  sym "("
  t <- pa
  sym ")"
  pure t

lit : Parser Term
lit = do
  t <- token Number
  pure $ Lit (LInt (cast t))



export
term : (Parser Term)


-- ( t : ty ), (t , u) (t)
-- Or do we want (x : ty)  I think we may need to annotate any term
parenThinger : Parser Term
parenThinger = do
  keyword "("
  t <- term
  -- And now we want ) : or ,
  -- we could do this with backtracing, but it'd kinda suck?
  fail "todo"

-- the inside of term
atom : Parser Term
atom = lit 
    <|> Var <$> ident
    <|> parens term
    -- <|> sym "(" *> term <* sym ")"

--
-- atom is lit or ident

data Fixity = InfixL | InfixR | Infix

-- starter pack, but we'll move some to prelude
operators : List (String, Int, Fixity)
operators = [
  ("->", 1, InfixR),
  ("=", 2, InfixL), -- REVIEW L R ?
  ("+",4,InfixL),
  ("-",4,InfixL),
  ("*",5,InfixL),
  ("/",5,InfixL)
]
parseApp : Parser Term
parseApp = do
  hd <- atom
  rest <- many atom
  pure $ foldl App hd rest
  

parseOp : Lazy (Parser Term)
parseOp = parseApp >>= go 0
  where
    go : Int -> Term -> Parser Term
    go prec left = 
      do
        op <- token Oper
        let Just (p,fix) = lookup op operators
         | Nothing => fail "expected operator"
        -- if p >= prec then pure () else fail ""
        guard $ p >= prec
        -- commit
        let pr = case fix of InfixR => p; _ => p + 1
        -- commit?
        right <- go pr !(parseApp)
        go prec (App (App (Var op) left) right)
      <|> pure left


export
letExpr : Parser Term
letExpr = do
  keyword "let"
  commit
  alts <- startBlock $ someSame $ letAssign
  keyword' "in"
  scope <- term
  pure $ Let alts scope
  -- Let <$ keyword "let" <*> ident <* keyword "=" <*> term <* keyword "in" <*> term

  where
    letAssign : Parser (Name,Term)
    letAssign = do
      name <- ident
      keyword "="
      t <- term
      pure (name,t)

pPattern : Parser Pattern
pPattern
   = PatWild <$ keyword "_"
  <|> PatVar <$> ident

export
lamExpr : Parser Term
lamExpr = do
  keyword "\\"
  commit
  name <- pPattern
  keyword "."
  scope <- term
  pure $ Lam name scope


caseAlt : Parser CaseAlt
caseAlt = do
  pat <- pPattern -- Term and sort it out later?
  keyword "=>"
  commit
  t <- term
  pure $ MkAlt pat t

export
caseExpr : Parser Term
caseExpr = do
  keyword "case"
  commit
  sc <- term
  keyword "of"
  alts <- startBlock $ someSame $ caseAlt
  pure $ Case sc alts


term = defer $ \_ => 
        caseExpr
    <|> letExpr
    <|> lamExpr
    <|> parseOp


-- And top level stuff

parseSig : Parser Decl
parseSig = TypeSig <$> ident <* keyword ":" <*> term

parseDef : Parser Decl
parseDef = Def <$> ident <* keyword "=" <*> term


parseDecl : Parser Decl
parseDecl = parseSig <|> parseDef

export
parseMod : Parser Module
parseMod = do
  keyword "module"
  name <- ident
  -- probably should be manySame, and we want to start with col -1
  -- if we enforce blocks indent
  decls <- startBlock $ someSame $ parseDecl
  pure $ MkModule name [] decls


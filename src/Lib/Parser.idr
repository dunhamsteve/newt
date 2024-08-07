module Lib.Parser
import Lib.Types

-- The FC stuff is awkward later on. We might want bounds on productions
-- But we might want to consider something more generic and closer to lean?

-- app: foo {a} a b
-- lam: λ {A} {b : A} (c : Blah) d e f => something
-- lam: \ {A} {b : A} (c : Blah) d e f => something
-- pi: (A : Set) -> {b : A} -> (c : Foo b) -> c -> bar d
-- pi: (A B : Set) {b : A} -> (c : Foo b) -> c -> bar d

import Lib.Token
import Lib.Parser.Impl
import Lib.Syntax
import Data.List
import Data.Maybe

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

braces : Parser a -> Parser a
braces pa = do
  sym "{"
  t <- pa
  sym "}"
  pure t


optional : Parser a -> Parser (Maybe a)
optional pa = Just <$> pa <|> pure Nothing

lit : Parser Raw
lit = do
  t <- token Number
  fc <- getFC
  pure $ RLit fc (LInt (cast t))

-- typeExpr is term with arrows.
export typeExpr : Parser Raw
export term : (Parser Raw)

-- the inside of Raw
atom : Parser Raw
atom = RU <$> getFC <* keyword "U"
    <|> RVar <$> getFC <*> ident
    <|> lit
    <|> RImplicit <$> getFC <* keyword "_"
    <|> RHole <$> getFC <* keyword "?"
    <|> parens typeExpr

-- Argument to a Spine
pArg : Parser (Icit,Raw)
pArg = (Explicit,) <$> atom <|> (Implicit,) <$> braces typeExpr


-- starter pack, but we'll move some to prelude
operators : List (String, Int, Fixity)
operators = [
  ("=",2,Infix),
  ("+",4,InfixL),
  ("-",4,InfixL),
  ("*",5,InfixL),
  ("/",5,InfixL)
]

parseApp : Parser Raw
parseApp = do
  hd <- atom
  rest <- many pArg
  fc <- getFC
  pure $ foldl (\a, (c,b) => RApp fc a b c) hd rest

parseOp : Parser Raw
parseOp = parseApp >>= go 0
  where
    go : Int -> Raw -> Parser Raw
    go prec left =
      do
        fc <- getFC
        op <- token Oper
        let Just (p,fix) = lookup op operators
         | Nothing => fail "expected operator"
        if p >= prec then pure () else fail ""
        let pr = case fix of InfixR => p; _ => p + 1
        right <- go pr !(parseApp)
        go prec (RApp fc (RApp fc (RVar fc op) left Explicit) right Explicit)
      <|> pure left

export
letExpr : Parser Raw
letExpr = do
  keyword "let"
  commit
  alts <- startBlock $ someSame $ letAssign
  keyword' "in"
  scope <- typeExpr
  fc <- getFC
  pure $ foldl (\ acc, (n,fc,v) => RLet fc n (RImplicit fc) v acc) scope alts
  where
    letAssign : Parser (Name,FC,Raw)
    letAssign = do
      fc <- getFC
      name <- ident
      -- TODO type assertion
      keyword "="
      t <- typeExpr
      pure (name,fc,t)

pLetArg : Parser (Icit, String, Maybe Raw)
pLetArg = (Implicit,,) <$> braces ident <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,) <$> parens ident <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,Nothing) <$> ident
       <|> (Explicit,"_",Nothing) <$ keyword "_"

-- lam: λ {A} {b : A} (c : Blah) d e f. something
export
lamExpr : Parser Raw
lamExpr = do
  keyword "\\" <|> keyword "λ"
  commit
  args <- some pLetArg
  keyword "=>"
  scope <- typeExpr
  fc <- getFC
  pure $ foldr (\(icit, name, ty), sc => RLam fc name icit sc) scope args

pPattern : Parser Pattern
pPattern
   = PatWild <$ keyword "_"
  <|> PatVar <$> ident


caseAlt : Parser RCaseAlt
caseAlt = do
  pat <- parseOp -- pPattern -- term and sort it out later?
  keyword "=>"
  commit
  t <- term
  pure $ MkAlt pat t

export
caseExpr : Parser Raw
caseExpr = do
  keyword "case"
  commit
  sc <- term
  keyword "of"
  alts <- startBlock $ someSame $ caseAlt
  pure $ RCase !(getFC) sc alts

-- This hits an idris codegen bug if parseOp is last and Lazy
term =  caseExpr
    <|> letExpr
    <|> lamExpr
    <|> parseOp


ebind : Parser (List (String, Icit, Raw))
ebind = do
  sym "("
  names <- some ident
  sym ":"
  ty <- typeExpr
  sym ")"
  pure $ map (\name => (name, Explicit, ty)) names

ibind : Parser (List (String, Icit, Raw))
ibind = do
  sym "{"
  mustWork $ do
    names <- some ident
    ty <- optional (sym ":" >> typeExpr)
    pos <- getFC
    sym "}"
    -- getFC is a hack here, I would like to position at the name...
    pure $ map (\name => (name, Implicit, fromMaybe (RImplicit pos) ty)) names

arrow : Parser Unit
arrow = sym "->" <|> sym "→"

-- Collect a bunch of binders (A : U) {y : A} -> ...
binders : Parser Raw
binders = do
  binds <- many (ibind <|> ebind)
  arrow
  commit
  scope <- typeExpr
  fc <- getFC
  pure $ foldr (mkBind fc) scope (join binds)
  where
    mkBind : FC -> (String, Icit, Raw) -> Raw -> Raw
    mkBind fc (name, icit, ty) scope = RPi fc (Just name) icit ty scope

typeExpr = binders
  <|> do
        exp <- term
        scope <- optional (arrow *> mustWork typeExpr)
        case scope of
          Nothing      => pure exp
          -- consider Maybe String to represent missing
          (Just scope) => pure $ RPi !(getFC) Nothing Explicit exp scope


-- And top level stuff


export
parseSig : Parser Decl
parseSig = TypeSig <$> getFC <*> ident <* keyword ":" <*> mustWork typeExpr

parseImport : Parser Decl
parseImport = DImport <$> getFC <* keyword "import" <* commit <*> ident

-- Do we do pattern stuff now? or just name = lambda?

export
parseDef : Parser Decl
parseDef = Def <$> getFC <*> ident <* keyword "=" <*> mustWork typeExpr

export
parseData : Parser Decl
parseData = do
  fc <- getFC
  keyword "data"
  name <- ident
  keyword ":"
  ty <- typeExpr
  keyword "where"
  commit
  decls <- startBlock $ manySame $ parseSig
  -- TODO - turn decls into something more useful
  pure $ Data fc name ty decls

-- Not sure what I want here.
-- I can't get a Tm without a type, and then we're covered by the other stuff
parseNorm : Parser Decl
parseNorm = DCheck <$> getFC <* keyword "#check" <*> typeExpr <* keyword ":" <*> typeExpr

export
parseDecl : Parser Decl
parseDecl = parseImport <|> parseSig <|> parseDef <|> parseNorm <|> parseData

export
parseMod : Parser Module
parseMod = do
  keyword "module"
  name <- ident
  -- probably should be manySame, and we want to start with col -1
  -- if we enforce blocks indent more than parent
  decls <- startBlock $ manySame $ parseDecl
  pure $ MkModule name decls

public export
data ReplCmd =
    Def Decl
  | Norm Raw -- or just name?
  | Check Raw


-- Eventually I'd like immediate actions in the file, like lean, but I
-- also want to REPL to work and we can do that first.
export parseRepl : Parser ReplCmd
parseRepl = Def <$> parseDecl <|> Norm <$ keyword "#nf" <*> typeExpr
  <|> Check <$ keyword "#check" <*> typeExpr

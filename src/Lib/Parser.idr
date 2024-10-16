module Lib.Parser
import Lib.Types
import Debug.Trace


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

ident = token Ident <|> token MixFix

uident = token UIdent

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

stringLit : Parser Raw
stringLit = do
  fc <- getPos
  t <- token StringKind
  pure $ RLit fc (LString (cast t))

intLit : Parser Raw
intLit = do
  fc <- getPos
  t <- token Number
  pure $ RLit fc (LInt (cast t))


lit : Parser Raw
lit = intLit <|> stringLit

-- typeExpr is term with arrows.
export typeExpr : Parser Raw
export term : (Parser Raw)

-- helpful when we've got some / many and need FC for each
withPos : Parser a -> Parser (FC, a)
withPos pa = (,) <$> getPos <*> pa

-- the inside of Raw
atom : Parser Raw
atom = RU <$> getPos <* keyword "U"
    <|> RVar <$> getPos <*> ident
    <|> RVar <$> getPos <*> uident
    <|> lit
    <|> RImplicit <$> getPos <* keyword "_"
    <|> RHole <$> getPos <* keyword "?"
    <|> parens typeExpr

-- Argument to a Spine
pArg : Parser (Icit,FC,Raw)
pArg = do
  fc <- getPos
  (Explicit,fc,) <$> atom <|> (Implicit,fc,) <$> braces typeExpr

parseApp : Parser Raw
parseApp = do
  fc <- getPos
  hd <- atom
  rest <- many pArg
  pure $ foldl (\a, (icit,fc,b) => RApp fc a b icit) hd rest

parseOp : Parser Raw
parseOp = parseApp >>= go 0
  where
    go : Int -> Raw -> Parser Raw
    go prec left =
      try (do
        fc <- getPos
        op <- token Oper
        ops <- getOps
        let op' = "_" ++ op ++ "_"
        let Just (p,fix) = lookup op' ops
          -- this is eaten, but we need `->` and `:=` to not be an operator to have fatal here
         | Nothing => case op of
         -- Location is poor on these because we pull off of the remaining token list...
          "->" => fail "no infix decl for \{op}"
          ":=" => fail "no infix decl for \{op}"
          op => fatal "no infix decl for \{op}"
        if p >= prec then pure () else fail ""
        let pr = case fix of InfixR => p; _ => p + 1
        right <- go pr !(parseApp)
        go prec (RApp fc (RApp fc (RVar fc op') left Explicit) right Explicit))
      <|> pure left

export
letExpr : Parser Raw
letExpr = do
  keyword "let"
  alts <- startBlock $ someSame $ letAssign
  keyword' "in"
  scope <- typeExpr
  pure $ foldl (\ acc, (n,fc,v) => RLet fc n (RImplicit fc) v acc) scope alts
  where
    letAssign : Parser (Name,FC,Raw)
    letAssign = do
      fc <- getPos
      name <- ident
      -- TODO type assertion
      keyword "="
      t <- typeExpr
      pure (name,fc,t)

pLetArg : Parser (Icit, String, Maybe Raw)
pLetArg = (Implicit,,) <$> braces (ident <|> uident) <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,) <$> parens (ident <|> uident) <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,Nothing) <$> (ident <|> uident)
       <|> (Explicit,"_",Nothing) <$ keyword "_"

-- lam: λ {A} {b : A} (c : Blah) d e f. something
export
lamExpr : Parser Raw
lamExpr = do
  keyword "\\" <|> keyword "λ"
  args <- some $ withPos pLetArg
  keyword "=>"
  scope <- typeExpr
  pure $ foldr (\(fc, icit, name, ty), sc => RLam fc name icit sc) scope args


-- Idris just has a term on the LHS and sorts it out later..
-- This allows some eval, like n + 2 -> S (S n), and expands to more complexity
-- like dotting

-- We may need to look up names at some point to see if they're constructors.

-- so, we can do the capital letter thing here or push that bit down and collect single/double
pPattern : Parser Pattern
patAtom : Parser Pattern
patAtom = do
  fc <- getPos
  PatWild fc Explicit <$ keyword "_"
    <|> PatVar fc Explicit <$> ident
    <|> PatCon fc Explicit <$> (uident <|> token MixFix) <*> pure []
    <|> braces (PatVar fc Implicit <$> ident)
    <|> braces (PatWild fc Implicit <$ keyword "_")
    <|> braces (PatCon fc Implicit <$> (uident <|> token MixFix) <*> many patAtom)
    <|> parens pPattern

pPattern = PatCon (!getPos) Explicit <$> (uident <|> token MixFix) <*> many patAtom <|> patAtom

caseAlt : Parser RCaseAlt
caseAlt = do
  pat <- typeExpr
  keyword "=>"
  t <- term
  pure $ MkAlt pat t

export
caseExpr : Parser Raw
caseExpr = do
  fc <- getPos
  keyword "case"
  sc <- term
  keyword "of"
  alts <- startBlock $ someSame $ caseAlt
  pure $ RCase fc sc alts

-- This hits an idris codegen bug if parseOp is last and Lazy
term =  caseExpr
    <|> letExpr
    <|> lamExpr
    <|> parseOp


ebind : Parser (List (FC, String, Icit, Raw))
ebind = do
  sym "("
  names <- some $ withPos (ident <|> uident)
  sym ":"
  ty <- typeExpr
  sym ")"
  pure $ map (\(pos, name) => (pos, name, Explicit, ty)) names

ibind : Parser (List (FC, String, Icit, Raw))
ibind = do
  sym "{"
  names <- some $ withPos (ident <|> uident)
  ty <- optional (sym ":" >> typeExpr)
  sym "}"
  pure $ map (\(pos,name) => (pos, name, Implicit, fromMaybe (RImplicit pos) ty)) names

arrow : Parser Unit
arrow = sym "->" <|> sym "→"

-- Collect a bunch of binders (A : U) {y : A} -> ...
binders : Parser Raw
binders = do
  binds <- many (ibind <|> try ebind)
  arrow
  scope <- typeExpr
  pure $ foldr (uncurry mkBind) scope (join binds)
  where
    mkBind : FC -> (String, Icit, Raw) -> Raw -> Raw
    mkBind fc (name, icit, ty) scope = RPi fc (Just name) icit ty scope

typeExpr = binders
  <|> do
        fc <- getPos
        exp <- term
        scope <- optional (arrow *> typeExpr)
        case scope of
          Nothing      => pure exp
          -- consider Maybe String to represent missing
          (Just scope) => pure $ RPi fc Nothing Explicit exp scope


-- And top level stuff


export
parseSig : Parser Decl
parseSig = TypeSig <$> getPos <*> (ident <|> uident) <* keyword ":" <*> typeExpr

parseImport : Parser Import
parseImport = MkImport <$> getPos <* keyword "import" <*> uident

-- Do we do pattern stuff now? or just name = lambda?

parseMixfix : Parser Decl
parseMixfix = do
  fc <- getPos
  fix <- InfixL <$ keyword "infixl"
     <|> InfixR <$ keyword "infixr"
     <|> Infix <$ keyword "infix"
  prec <- token Number
  op <- token MixFix
  addOp op (cast prec) fix
  pure $ PMixFix fc op (cast prec) fix

getName : Raw -> Parser String
getName (RVar x nm) = pure nm
getName (RApp x t u icit) = getName t
getName tm = fail "bad LHS"


export
parseDef : Parser Decl
parseDef = do
  fc <- getPos
  t <- typeExpr
  nm <- getName t
  -- nm <- ident <|> uident
  pats <- many patAtom
  keyword "="
  body <- typeExpr
  -- these get collected later
  pure $ Def fc nm [(t, body)] -- [MkClause fc [] t body]

export
parsePType : Parser Decl
parsePType = do
  fc <- getPos
  keyword "ptype"
  id <- uident
  ty <- optional $ do
    keyword ":"
    typeExpr
  pure $ PType fc id ty

parsePFunc : Parser Decl
parsePFunc = do
  fc <- getPos
  keyword "pfunc"
  nm <- ident
  keyword ":"
  ty <- typeExpr
  keyword ":="
  src <- cast <$> token StringKind
  pure $ PFunc fc nm ty src

export
parseData : Parser Decl
parseData = do
  fc <- getPos
  keyword "data"
  name <- uident <|> token MixFix
  keyword ":"
  ty <- typeExpr
  keyword "where"
  decls <- startBlock $ manySame $ parseSig
  pure $ Data fc name ty decls

-- Not sure what I want here.
-- I can't get a Tm without a type, and then we're covered by the other stuff
parseNorm : Parser Decl
parseNorm = DCheck <$> getPos <* keyword "#check" <*> typeExpr <* keyword ":" <*> typeExpr

export
parseDecl : Parser Decl
parseDecl = parseMixfix <|> parsePType <|> parsePFunc <|> parseNorm <|> parseData <|> (try $ parseSig) <|> parseDef

export
parseMod : Parser Module
parseMod = do
  keyword "module"
  name <- uident
  startBlock $ do
    imports <- manySame $ parseImport
    decls <- manySame $ parseDecl
    pure $ MkModule name imports decls

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

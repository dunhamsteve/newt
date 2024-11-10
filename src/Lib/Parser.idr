module Lib.Parser
import Lib.Types
import Debug.Trace
import Data.String

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

dbraces : Parser a -> Parser a
dbraces pa = do
  sym "{{"
  t <- pa
  sym "}}"
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


charLit : Parser Raw
charLit = do
  fc <- getPos
  v <- token Character
  pure $ RLit fc (LChar $ assert_total $ strIndex v 1)

lit : Parser Raw
lit = intLit <|> stringLit <|> charLit

-- typeExpr is term with arrows.
export typeExpr : Parser Raw
export term : (Parser Raw)

-- helpful when we've got some / many and need FC for each
withPos : Parser a -> Parser (FC, a)
withPos pa = (,) <$> getPos <*> pa

lookup : String -> List OpDef -> Maybe OpDef
lookup _ [] = Nothing
lookup name (op :: ops) = if op.name == name then Just op else lookup name ops

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
  (Explicit,fc,) <$> atom
    <|> (Implicit,fc,) <$> braces typeExpr
    <|> (Auto,fc,) <$> dbraces typeExpr

AppSpine = List (Icit,FC,Raw)

pratt : List OpDef -> Int -> Raw -> AppSpine -> Parser (Raw, AppSpine)
pratt ops prec left [] = pure (left, [])
pratt ops prec left rest@((Explicit, fc, tm@(RVar x nm)) :: xs) =
  let op' = ("_" ++ nm ++ "_") in
  case lookup op' ops of
    Nothing => pratt ops prec (RApp fc left tm Explicit) xs
    Just (MkOp name p fix) => if p < prec
      then pure (left, rest)
      else
        let pr = case fix of InfixR => p; _ => p + 1 in
        case xs of
          ((_, _, right) :: rest) => do
            (right, rest) <- pratt ops pr right rest
            pratt ops prec (RApp fc(RApp fc (RVar fc op') left Explicit) right Explicit) rest
          _ => fail "trailing operator"
pratt ops prec left ((icit, fc, tm) :: xs) = pratt ops prec (RApp fc left tm icit) xs

parseOp : Parser Raw
parseOp = do
  fc <- getPos
  ops <- getOps
  hd <- atom
  rest <- many pArg
  (res, []) <- pratt ops 0 hd rest
    | _ => fail "extra stuff"
  pure res

export
letExpr : Parser Raw
letExpr = do
  keyword "let"
  alts <- startBlock $ someSame $ letAssign
  keyword' "in"
  scope <- typeExpr
  pure $ foldl (\ acc, (n,fc,v) => RLet fc n (RImplicit fc) v acc) scope (reverse alts)
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
       <|> (Auto,,) <$> dbraces (ident <|> uident) <*> optional (sym ":" >> typeExpr)
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
    <|> dbraces (PatVar fc Auto <$> ident)
    <|> dbraces (PatWild fc Auto <$ keyword "_")
    <|> dbraces (PatCon fc Auto <$> (uident <|> token MixFix) <*> many patAtom)
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

doStmt : Parser DoStmt
doStmt
  = DoArrow <$> getPos <*> (try $ ident <* keyword "<-") <*> term
  <|> DoLet <$> getPos <* keyword "let" <*> ident <* keyword "=" <*> term
  <|> DoExpr <$> getPos <*> term

doExpr : Parser Raw
doExpr = RDo <$> getPos <* keyword "do" <*> (startBlock $ someSame doStmt)


-- This hits an idris codegen bug if parseOp is last and Lazy
term =  caseExpr
    <|> letExpr
    <|> lamExpr
    <|> doExpr
    <|> parseOp

varname : Parser String
varname = (ident <|> uident <|> keyword "_" *> pure "_")

ebind : Parser (List (FC, String, Icit, Raw))
ebind = do
  -- don't commit until we see the ":"
  sym "("
  names <- try (some (withPos varname) <* sym ":")
  ty <- typeExpr
  sym ")"
  pure $ map (\(pos, name) => (pos, name, Explicit, ty)) names

ibind : Parser (List (FC, String, Icit, Raw))
ibind = do
  sym "{"
  -- REVIEW - I have name required and type optional, which I think is the opposite of what I expect
  names <- try (some (withPos varname) <* sym ":")
  ty <- typeExpr
  sym "}"
  pure $ map (\(pos,name) => (pos, name, Implicit, ty)) names

abind : Parser (List (FC, String, Icit, Raw))
abind = do
  sym "{{"
  names <- try (some (withPos varname) <* sym ":")
  ty <- typeExpr
  sym "}}"
  pure $ map (\(pos,name) => (pos, name, Auto, ty)) names

arrow : Parser Unit
arrow = sym "->" <|> sym "→"

-- Collect a bunch of binders (A : U) {y : A} -> ...

forAll : Parser Raw
forAll = do
  keyword "forall" <|> keyword "∀"
  all <- some (withPos varname)
  keyword "."
  scope <- typeExpr
  pure $ foldr (\ (fc, n), sc => RPi fc (Just n) Implicit (RImplicit fc) sc) scope all

binders : Parser Raw
binders = do
  binds <- many (abind <|> ibind <|> ebind)
  arrow
  scope <- typeExpr
  pure $ foldr (uncurry mkBind) scope (join binds)
  where
    mkBind : FC -> (String, Icit, Raw) -> Raw -> Raw
    mkBind fc (name, icit, ty) scope = RPi fc (Just name) icit ty scope

typeExpr
  = binders
  <|> forAll
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
parseSig = TypeSig <$> getPos <*> try (some (ident <|> uident) <* keyword ":") <*> typeExpr

parseImport : Parser Import
parseImport = MkImport <$> getPos <* keyword "import" <*> uident

-- Do we do pattern stuff now? or just name = lambda?
-- TODO multiple names
parseMixfix : Parser Decl
parseMixfix = do
  fc <- getPos
  fix <- InfixL <$ keyword "infixl"
     <|> InfixR <$ keyword "infixr"
     <|> Infix <$ keyword "infix"
  prec <- token Number
  ops <- some $ token MixFix
  for_ ops $ \ op => addOp op (cast prec) fix
  pure $ PMixFix fc ops (cast prec) fix

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
parseDecl = parseMixfix <|> parsePType <|> parsePFunc <|> parseNorm <|> parseData <|> parseSig <|> parseDef


export
parseModHeader : Parser String
parseModHeader = sameLevel (keyword "module") >> uident

export
parseImports : Parser (List Import)
parseImports = manySame $ parseImport

export
parseMod : Parser Module
parseMod = do
  startBlock $ do
    keyword "module"
    name <- uident
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

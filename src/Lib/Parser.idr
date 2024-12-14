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
  pure $ RLit fc (LChar $ assert_total $ strIndex v 0)

lit : Parser Raw
lit = intLit <|> stringLit <|> charLit

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
  (Explicit,fc,) <$> atom
    <|> (Implicit,fc,) <$> braces typeExpr
    <|> (Auto,fc,) <$> dbraces typeExpr

AppSpine = List (Icit,FC,Raw)

-- helper for debugging
traceM : Monad m => String -> m ()
traceM msg = trace msg $ pure ()

pratt : Operators -> Int -> String -> Raw -> AppSpine -> Parser (Raw, AppSpine)
pratt ops prec stop left spine = do
  (left, spine) <- runPrefix stop left spine
  case spine of
    [] => pure (left, [])
    ((Explicit, fc, tm@(RVar x nm)) :: rest) =>
        if nm == stop then pure (left,spine) else
        case lookup nm ops of
          Just (MkOp name p fix False rule) => if p < prec
            then pure (left, spine)
            else
              runRule p fix stop rule (RApp fc (RVar fc name) left Explicit) rest
          Just _ => fail "expected operator"
          Nothing => pratt ops prec stop (RApp (getFC left) left tm Explicit) rest
    ((icit, fc, tm) :: rest) => pratt ops prec stop (RApp (getFC left) left tm icit) rest
  where
    runRule : Int -> Fixity -> String -> List String -> Raw -> AppSpine -> Parser (Raw,AppSpine)
    runRule p fix stop [] left spine = pure (left,spine)
    runRule p fix stop [""] left spine = do
      let pr = case fix of InfixR => p; _ => p + 1
      case spine of
                ((_, fc, right) :: rest) => do
                  (right, rest) <- pratt ops pr stop right rest
                  pratt ops prec stop (RApp (getFC left) left right Explicit) rest
                _ => fail "trailing operator"

    runRule p fix stop (nm :: rule) left spine = do
      let ((_,_,right)::rest) = spine | _ => fail "short"
      (right,rest) <- pratt ops 0 nm right rest -- stop!!
      let ((_,fc',RVar fc name) :: rest) = rest
        | _ => fail "expected \{nm}"

      if name == nm
          then runRule p fix stop rule (RApp (getFC left) left right Explicit) rest
          else fail "expected \{nm}"


    runPrefix : String -> Raw -> AppSpine -> Parser (Raw, AppSpine)
    runPrefix stop (RVar fc nm) spine =
      case lookup nm ops of
           -- TODO False should be an error here
         Just (MkOp name p fix True rule) => do
            runRule p fix stop rule (RVar fc name) spine
         _ => pure (left, spine)
    runPrefix stop left spine = pure (left, spine)

parseOp : Parser Raw
parseOp = do
  fc <- getPos
  ops <- getOps
  hd <- atom
  rest <- many pArg
  (res, []) <- pratt ops 0 "" hd rest
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

pLamArg : Parser (Icit, String, Maybe Raw)
pLamArg = (Implicit,,) <$> braces (ident <|> uident) <*> optional (sym ":" >> typeExpr)
       <|> (Auto,,) <$> dbraces (ident <|> uident) <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,) <$> parens (ident <|> uident) <*> optional (sym ":" >> typeExpr)
       <|> (Explicit,,Nothing) <$> (ident <|> uident)
       <|> (Explicit,"_",Nothing) <$ keyword "_"

-- lam: λ {A} {b : A} (c : Blah) d e f. something
export
lamExpr : Parser Raw
lamExpr = do
  pos <- getPos
  keyword "\\" <|> keyword "λ"
  args <- some $ withPos pLamArg
  keyword "=>"
  scope <- typeExpr
  pure $ foldr (\(fc, icit, name, ty), sc => RLam pos (BI fc name icit Many) sc) scope args

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

doExpr : Parser Raw
doStmt : Parser DoStmt

caseLet : Parser Raw
caseLet = do
  -- look ahead so we can fall back to normal let
  fc <- getPos
  try (keyword "let" >> sym "(")
  pat <- typeExpr
  sym ")"
  keyword "="
  sc <- typeExpr
  alts <- startBlock $ manySame $ sym "|" *> caseAlt
  keyword "in"
  body <- term
  pure $ RCase fc sc (MkAlt pat body :: alts)

doCaseLet : Parser DoStmt
doCaseLet = do
  -- look ahead so we can fall back to normal let
  -- Maybe make it work like arrow?
  fc <- getPos
  try (keyword "let" >> sym "(")
  pat <- typeExpr
  sym ")"
  keyword "="
  -- arrow <- (False <$ keyword "=" <|> True <$ keyword "<-")
  sc <- typeExpr
  alts <- startBlock $ manySame $ sym "|" *> caseAlt
  bodyFC <- getPos
  body <- RDo <$> getPos <*> someSame doStmt
  pure $ DoExpr fc (RCase fc sc (MkAlt pat body :: alts))

doArrow : Parser DoStmt
doArrow = do
  fc <- getPos
  left <- typeExpr
  Just _ <- optional $ keyword "<-"
    | _ => pure $ DoExpr fc left
  right <- term
  alts <- startBlock $ manySame $ sym "|" *> caseAlt
  pure $ DoArrow fc left right alts

doStmt
  = doCaseLet
  <|> DoLet <$> getPos <* keyword "let" <*> ident <* keyword "=" <*> term
  <|> doArrow

doExpr = RDo <$> getPos <* keyword "do" <*> (startBlock $ someSame doStmt)

ifThenElse : Parser Raw
ifThenElse = do
  fc <- getPos
  keyword "if"
  a <- term
  keyword "then"
  b <- term
  keyword "else"
  c <- term
  pure $ RIf fc a b c

term' : Parser Raw

term' =  caseExpr
    <|> caseLet
    <|> letExpr
    <|> lamExpr
    <|> doExpr
    <|> ifThenElse
    -- Make this last for better error messages
    <|> parseOp

term = do
  t <- term'
  rest <- many ((,) <$> getPos <* keyword "$" <*> term')
  pure $ apply t rest
  where
    apply : Raw -> List (FC,Raw) -> Raw
    apply t [] = t
    apply t ((fc,x) :: xs) = RApp fc t (apply x xs) Explicit

varname : Parser String
varname = (ident <|> uident <|> keyword "_" *> pure "_")

quantity : Parser Quant
quantity = fromMaybe Many <$> optional (Zero <$ keyword "0")

ebind : Parser Telescope
ebind = do
  -- don't commit until we see the ":"
  sym "("
  quant <- quantity
  names <- try (some (withPos varname) <* sym ":")
  ty <- typeExpr
  sym ")"
  pure $ map (\(pos, name) => (BI pos name Explicit quant, ty)) names

ibind : Parser Telescope
ibind = do
  -- I've gone back and forth on this, but I think {m a b} is more useful than {Nat}
  sym "{"
  quant <- quantity
  names <- (some (withPos varname))
  ty <- optional (sym ":" *> typeExpr)
  sym "}"
  pure $ map (\(pos,name) => (BI pos name Implicit quant, fromMaybe (RImplicit pos) ty)) names

abind : Parser Telescope
abind = do
  -- for this, however, it would be nice to allow {{Monad A}}
  sym "{{"
  name <- optional $ try (withPos varname <* sym ":")
  ty <- typeExpr
  sym "}}"
  case name of
    Just (pos,name) => pure [(BI pos name Auto Many, ty)]
    Nothing => pure [(BI (getFC ty) "_" Auto Many, ty)]

arrow : Parser Unit
arrow = sym "->" <|> sym "→"

-- Collect a bunch of binders (A : U) {y : A} -> ...

forAll : Parser Raw
forAll = do
  keyword "forall" <|> keyword "∀"
  all <- some (withPos varname)
  keyword "."
  scope <- typeExpr
  pure $ foldr (\ (fc, n), sc => RPi fc (BI fc n Implicit Zero) (RImplicit fc) sc) scope all

binders : Parser Raw
binders = do
  binds <- many (abind <|> ibind <|> ebind)
  arrow
  scope <- typeExpr
  pure $ foldr mkBind scope (join binds)
  where
    mkBind : (BindInfo, Raw) -> Raw -> Raw
    mkBind (info, ty) scope = RPi (getFC info) info ty scope

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
          (Just scope) => pure $ RPi fc (BI fc "_" Explicit Many) exp scope

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
  keyword "="
  body <- typeExpr
  wfc <- getPos
  w <- optional $ do
    keyword "where"
    startBlock $ manySame $ (parseSig <|> parseDef)
  let body = maybe body (\ decls => RWhere wfc decls body) w
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
  uses <- optional (keyword "uses" >> parens (many $ uident <|> ident <|> token MixFix))
  keyword ":"
  ty <- typeExpr
  keyword ":="
  src <- cast <$> token JSLit
  pure $ PFunc fc nm (fromMaybe [] uses) ty src

export
parseData : Parser Decl
parseData = do
  fc <- getPos
  keyword "data"
  name <- uident <|> ident <|> token MixFix
  keyword ":"
  ty <- typeExpr
  keyword "where"
  decls <- startBlock $ manySame $ parseSig
  pure $ Data fc name ty decls

nakedBind : Parser Telescope
nakedBind = do
  names <- some (withPos varname)
  pure $ map (\(pos,name) => (BI pos name Explicit Many, RImplicit pos)) names

export
parseClass : Parser Decl
parseClass = do
  fc <- getPos
  keyword "class"
  name <- uident
  teles <- many $ ebind <|> nakedBind
  keyword "where"
  decls <- startBlock $ manySame $ parseSig
  pure $ Class fc name (join teles) decls

export
parseInstance : Parser Decl
parseInstance = do
  fc <- getPos
  keyword "instance"
  ty <- typeExpr
  keyword "where"
  decls <- startBlock $ manySame $ parseDef
  pure $ Instance fc ty decls

-- Not sure what I want here.
-- I can't get a Tm without a type, and then we're covered by the other stuff
parseNorm : Parser Decl
parseNorm = DCheck <$> getPos <* keyword "#check" <*> typeExpr <* keyword ":" <*> typeExpr

export
parseDecl : Parser Decl
parseDecl = parseMixfix <|> parsePType <|> parsePFunc
  <|> parseNorm <|> parseData <|> parseSig <|> parseDef
  <|> parseClass <|> parseInstance


export
parseModHeader : Parser (FC, String)
parseModHeader = sameLevel (keyword "module") >> withPos uident

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

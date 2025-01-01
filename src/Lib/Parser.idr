module Lib.Parser

import Data.Maybe
import Data.String
import Lib.Parser.Impl
import Lib.Syntax
import Lib.Token
import Lib.Types

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


-- typeExpr is term with arrows.
export typeExpr : Parser Raw
export term : (Parser Raw)

interp : Parser Raw
interp = token StartInterp *> term <* token EndInterp


interpString : Parser Raw
interpString = do
  fc <- getPos
  ignore $ token StartQuote
  part <- term
  parts <- many (stringLit <|> interp)
  ignore $ token EndQuote
  pure $ foldl append part parts
  where
    append : Raw -> Raw -> Raw
    append t u =
      let fc = getFC t in
      (RApp fc (RApp fc (RVar fc "_++_") t Explicit) u Explicit)

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
lit = intLit <|> interpString <|> stringLit <|> charLit



-- helpful when we've got some / many and need FC for each
withPos : Parser a -> Parser (FC, a)
withPos pa = (,) <$> getPos <*> pa

asAtom : Parser Raw
asAtom = do
  fc <- getPos
  nm <- ident
  asPat <- optional $ keyword "@" *> parens typeExpr
  case asPat of
    Just exp => pure $ RAs fc nm exp
    Nothing  => pure $ RVar fc nm

-- the inside of Raw
atom : Parser Raw
atom = RU <$> getPos <* keyword "U"
    -- <|> RVar <$> getPos <*> ident
    <|> asAtom
    <|> RVar <$> getPos <*> uident
    <|> RVar <$> getPos <*> token Projection
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

pratt : Operators -> Int -> String -> Raw -> AppSpine -> Parser (Raw, AppSpine)
pratt ops prec stop left spine = do
  (left, spine) <- runPrefix stop left spine
  let spine = runProject spine
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
          Nothing =>
            if isPrefixOf "." nm
            then pratt ops prec stop (RApp (getFC tm) tm left Explicit) rest
            else pratt ops prec stop (RApp (getFC left) left tm Explicit) rest
    ((icit, fc, tm) :: rest) => pratt ops prec stop (RApp (getFC left) left tm icit) rest
  where
    -- we have a case above for when the next token is a projection, but
    -- we need this to make projection bind tighter than app
    runProject : AppSpine -> AppSpine
    runProject (t@(Explicit, fc', tm) :: u@(Explicit, _, RVar fc nm) :: rest) =
      if isPrefixOf "." nm
        then runProject ((Explicit, fc', RApp fc (RVar fc nm) tm Explicit) :: rest)
        else (t :: u :: rest)
    runProject tms = tms

    -- left has our partially applied operator and we're picking up args
    -- for the rest of the `_`
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

    -- run any prefix operators
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


-- TODO case let? We see to only have it for `do`
-- try (keyword "let" >> sym "(")

export
letExpr : Parser Raw
letExpr = do
  keyword "let"
  alts <- startBlock $ someSame $ letAssign
  keyword' "in"
  scope <- typeExpr
  pure $ foldl (\ acc, (n,fc,ty,v) => RLet fc n (fromMaybe (RImplicit fc) ty) v acc) scope (reverse alts)
  where
    letAssign : Parser (Name,FC,Maybe Raw,Raw)
    letAssign = do
      fc <- getPos
      name <- ident
      -- TODO type assertion
      ty <- optional (keyword ":" *> typeExpr)
      keyword "="
      t <- typeExpr
      pure (name,fc,ty,t)

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

caseLamExpr : Parser Raw
caseLamExpr = do
  fc <- getPos
  try ((keyword "\\" <|> keyword "λ") *> keyword "case")
  alts <- startBlock $ someSame $ caseAlt
  pure $ RLam fc (BI fc "$case" Explicit Many) $ RCase fc (RVar fc "$case") alts

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
    <|> caseLamExpr
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
parseSig = TypeSig <$> getPos <*> try (some (ident <|> uident <|> token Projection) <* keyword ":") <*> typeExpr

parseImport : Parser Import
parseImport = do
  fc <- getPos
  keyword "import"
  ident <- uident
  rest <- many $ token Projection
  let name = joinBy "" (ident :: rest)
  pure $ MkImport fc name

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


parseShortData : Parser Decl
parseShortData = do
  fc <- getPos
  keyword "data"
  lhs <- typeExpr
  keyword "="
  sigs <- sepBy (keyword "|") typeExpr
  pure $ ShortData fc lhs sigs

export
parseData : Parser Decl
parseData = do
  fc <- getPos
  -- commit when we hit ":"
  name <- try $ (keyword "data" *> (uident <|> ident <|> token MixFix) <* keyword ":")
  ty <- typeExpr
  keyword "where"
  decls <- startBlock $ manySame $ parseSig
  pure $ Data fc name ty decls

nakedBind : Parser Telescope
nakedBind = do
  names <- some (withPos varname)
  pure $ map (\(pos,name) => (BI pos name Explicit Many, RImplicit pos)) names

export
parseRecord : Parser Decl
parseRecord = do
  fc <- getPos
  keyword "record"
  name <- uident
  teles <- many $ ebind <|> nakedBind
  keyword "where"
  cname <- optional $ keyword "constructor" *> (uident <|> token MixFix)
  decls <- startBlock $ manySame $ parseSig
  pure $ Record fc name (join teles) cname decls


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
  <|> parseNorm <|> parseData <|> parseShortData <|> parseSig <|> parseDef
  <|> parseClass <|> parseInstance <|> parseRecord


export
parseModHeader : Parser (FC, String)
parseModHeader = do
  sameLevel (keyword "module")
  fc <- getPos
  name <- uident
  rest <- many $ token Projection
  -- FIXME use QName
  let name = joinBy "" (name :: rest)
  pure (fc, name)

export
parseImports : Parser (List Import)
parseImports = manySame $ parseImport

export
parseMod : Parser Module
parseMod = do
  startBlock $ do
    keyword "module"
    name <- uident
    rest <- many $ token Projection
    -- FIXME use QName
    let name = joinBy "" (name :: rest)
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

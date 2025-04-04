-- TODO Audit how much "outside" stuff could pile up in the continuation.
module Lib.Compile

import Lib.Types
import Lib.Prettier
import Lib.CompileExp
import Lib.TopContext
import Data.String
import Data.Maybe
import Data.Nat

data Kind = Plain | Return | Assign String

data JSStmt : Kind -> Type
data JSExp : Type

data JAlt : Type where
  JConAlt : String -> JSStmt e -> JAlt
  JDefAlt : JSStmt e -> JAlt
  JLitAlt : JSExp -> JSStmt e -> JAlt

data JSExp : Type where
  LitArray : List JSExp -> JSExp
  LitObject : List (String, JSExp) -> JSExp
  LitString : String -> JSExp
  LitInt : Int -> JSExp
  Apply : JSExp -> List JSExp -> JSExp
  Var : String -> JSExp
  JLam : List String -> JSStmt Return -> JSExp
  JUndefined : JSExp
  Index : JSExp -> JSExp -> JSExp
  Dot : JSExp -> String -> JSExp

data JSStmt : Kind -> Type where
  -- Maybe make this a snoc...
  JSnoc : JSStmt Plain -> JSStmt a -> JSStmt a
  JPlain : JSExp -> JSStmt Plain
  JConst : (nm : String) -> JSExp -> JSStmt Plain
  JReturn : JSExp -> JSStmt Return
  JLet : (nm : String) -> JSStmt (Assign nm) -> JSStmt Plain  -- need somebody to assign
  JAssign : (nm : String) -> JSExp -> JSStmt (Assign nm)
  -- TODO - switch to Nat tags
  -- FIXME add e to JAlt (or just drop it?)
  JCase : JSExp -> List JAlt -> JSStmt a
  -- throw can't be used
  JError : String -> JSStmt a

Cont e = JSExp -> JSStmt e

||| JSEnv contains `Var` for binders or `Dot` for destructured data. It
||| used to translate binders
record JSEnv where
  constructor MkEnv
  env : List JSExp
  depth : Nat

push : JSEnv -> JSExp -> JSEnv
push env exp = { env $= (exp ::) } env

empty : JSEnv
empty = MkEnv [] Z

litToJS : Literal -> JSExp
litToJS (LString str) = LitString str
litToJS (LChar c) = LitString $ cast c
litToJS (LInt i) = LitInt i

-- Stuff nm.h1, nm.h2, ... into environment
-- TODO consider JSExp instead of nm, so we can have $foo.h1 instead of assigning a sc.
mkEnv : String -> Nat -> JSEnv -> List String -> JSEnv
mkEnv nm k env [] = env
mkEnv nm k env (x :: xs) = mkEnv nm (S k) (push env (Dot (Var nm) "h\{show k}")) xs

envNames : Env -> List String

||| given a name, find a similar one that doesn't shadow in Env
freshName : String -> JSEnv -> String
freshName nm env = if free env.env nm then nm else go nm 1
  where
    free : List JSExp -> String -> Bool
    free [] nm = True
    free (Var n :: xs) nm = if n == nm then False else free xs nm
    free (_ :: xs) nm = free xs nm

    go : String -> Nat -> String
    go nm k = let nm' = "\{nm}\{show k}" in if free env.env nm' then nm' else go nm (S k)

freshName' : String -> JSEnv -> (String, JSEnv)
freshName' nm env =
  let nm' = freshName nm env -- "\{nm}$\{show $ length env}"
      env' = push env (Var nm')
  in (nm', env')

freshNames : List String -> JSEnv -> (List String, JSEnv)
freshNames nms env = go nms env [<]
  where
    go : List Name -> JSEnv -> SnocList Name -> (List String, JSEnv)
    go Nil env acc = (acc <>> Nil, env)
    go (n :: ns) env acc =
      let (n', env') = freshName' n env
      in go ns env' (acc :< n')

-- This is inspired by A-normalization, look into the continuation monad
-- There is an index on JSStmt, adopted from Stefan Hoeck's code.
--
-- Here we turn a Term into a statement (which may be a sequence of statements), there
-- is a continuation, which turns the final JSExpr into a JSStmt, and the function returns
-- a JSStmt, wrapping recursive calls in JSnoc if necessary.
termToJS : JSEnv -> CExp -> Cont e -> JSStmt e
termToJS env (CBnd k) f = case getAt k env.env of
  (Just e) => f e
  Nothing => ?bad_bounds
termToJS env CErased f = f JUndefined
termToJS env (CLam nm t) f =
  let (nm',env') = freshName' nm env -- "\{nm}$\{show $ length env}"
  in f $ JLam [nm'] (termToJS env' t JReturn)
termToJS env (CFun nms t) f =
  let (nms', env') = freshNames nms env
  in f $ JLam nms' (termToJS env' t JReturn)
termToJS env (CRef nm) f = f $ Var nm
termToJS env (CMeta k) f = f $ LitString "META \{show k}"
termToJS env (CLit lit) f = f (litToJS lit)
-- if it's a var, just use the original
termToJS env (CLet nm (CBnd k) u) f = case getAt k env.env of
  Just e  => termToJS (push env e) u f
  Nothing => ?bad_bounds2
termToJS env (CLet nm t u) f =
  let nm' = freshName nm env
      env' = push env (Var nm')
  -- If it's a simple term, use const
  in case termToJS env t (JAssign nm') of
    (JAssign _ exp) => JSnoc (JConst nm' exp) (termToJS env' u f)
    t' => JSnoc (JLet nm' t') (termToJS env' u f)
termToJS env (CLetRec nm t u) f =
  let nm' = freshName nm env
      env' = push env (Var nm')
  -- If it's a simple term, use const
  in case termToJS env' t (JAssign nm') of
    (JAssign _ exp) => JSnoc (JConst nm' exp) (termToJS env' u f)
    t' => JSnoc (JLet nm' t') (termToJS env' u f)

termToJS env (CApp t args etas) f = termToJS env t (\ t' => (argsToJS t' args [<] f)) --  (f (Apply t' args'))))
  where
    etaExpand : JSEnv -> Nat -> SnocList JSExp -> JSExp -> JSExp
    etaExpand env Z args tm = Apply tm (args <>> [])
    etaExpand env (S etas) args tm =
      let nm' = freshName "eta" env
          env' = push env (Var nm')
       in JLam [nm'] $ JReturn $ etaExpand (push env (Var nm')) etas (args :< Var nm') tm

    argsToJS : JSExp -> List CExp -> SnocList JSExp -> (JSExp -> JSStmt e) -> JSStmt e
    argsToJS tm [] acc k = k (etaExpand env etas acc tm)
    -- k (acc <>> [])
    argsToJS tm (x :: xs) acc k = termToJS env x (\ x' => argsToJS tm xs (acc :< x') k)


termToJS env (CCase t alts) f =
  -- need to assign the scrutinee to a variable (unless it is a var already?)
  -- and add (Bnd -> JSExpr map)
  -- TODO default case, let's drop the extra field.

  termToJS env t $ \case
    (Var nm) => maybeCaseStmt env nm alts
    t' => do
      -- TODO refactor nm to be a JSExp with Var{} or Dot{}
      -- FIXME sc$ seemed to shadow something else, lets get this straightened out
      -- we need freshName names that are not in env (i.e. do not play in debruijn)
      let nm = "_sc$\{show env.depth}"
      let env' = { depth $= S } env
      JSnoc (JConst nm t') (maybeCaseStmt env' nm alts)

  where
    termToJSAlt : JSEnv -> String -> CAlt -> JAlt
    termToJSAlt env nm (CConAlt name args u) = JConAlt name (termToJS (mkEnv nm 0 env args) u f)
    -- intentionally reusing scrutinee name here
    termToJSAlt env nm (CDefAlt u) = JDefAlt (termToJS  (env) u f)
    termToJSAlt env nm (CLitAlt lit u) = JLitAlt (litToJS lit) (termToJS env u f)

    maybeCaseStmt : JSEnv -> String -> List CAlt -> JSStmt e
    -- If there is a single alt, assume it matched
    maybeCaseStmt env nm [(CConAlt _ args u)] = (termToJS (mkEnv nm 0 env args) u f)
    maybeCaseStmt env nm alts@(CLitAlt _ _  :: _) =
        (JCase (Var nm) (map (termToJSAlt env nm) alts))
    maybeCaseStmt env nm alts =
          (JCase (Dot (Var nm) "tag") (map (termToJSAlt env nm) alts))

jsKeywords : List String
jsKeywords = [
  "break", "case", "catch", "continue", "debugger", "default", "delete", "do", "else",
  "finally", "for", "function", "if", "in", "instanceof", "new", "return", "switch",
  "this", "throw", "try", "typeof", "var", "void", "while", "with",
  "class", "const", "enum", "export", "extends", "import", "super",
  "implements", "interface", "let", "package", "private", "protected", "public",
  "static", "yield",
  "null", "true", "false",
  -- might not be a big issue with namespaces on names now.
  "String", "Number", "Array", "BigInt"
]

||| escape identifiers for js
jsIdent : String -> Doc
jsIdent id = if elem id jsKeywords then text ("$" ++ id) else text $ pack $ fix (unpack id)
  where
    fix : List Char -> List Char
    fix [] = []
    fix (x :: xs) =
      if isAlphaNum x || x == '_' then
        x :: fix xs
      -- make qualified names more readable
      else if x == '.' then '_' :: fix xs
      else if x == '$' then
        '$' :: '$' :: fix xs
      else
        '$' :: (toHex (cast x)) ++ fix xs

stmtToDoc : JSStmt e -> Doc


expToDoc : JSExp -> Doc
expToDoc (LitArray xs) = ?expToDoc_rhs_0
expToDoc (LitObject xs) = text "{" <+> folddoc (\ a, e => a ++ text ", " <+/> e) (map entry xs) <+> text "}"
  where
    entry : (String, JSExp) -> Doc
    -- TODO quote if needed
    entry (nm, exp) = jsIdent nm ++ text ":" <+> expToDoc exp

expToDoc (LitString str) = text $ quoteString str
expToDoc (LitInt i) = text $ show i
-- TODO add precedence
expToDoc (Apply x@(JLam{}) xs) = text "(" ++ expToDoc x ++ text ")" ++ text "(" ++ nest 2 (commaSep (map expToDoc xs)) ++ text ")"
expToDoc (Apply x xs) = expToDoc x ++ text "(" ++ nest 2 (commaSep (map expToDoc xs)) ++ text ")"
expToDoc (Var nm) = jsIdent nm
expToDoc (JLam nms (JReturn exp)) = text "(" <+> commaSep (map jsIdent nms) <+> text ") =>" <+> text "(" ++ expToDoc exp ++ text ")"
expToDoc (JLam nms body) = text "(" <+> commaSep (map jsIdent nms) <+> text ") =>" <+> bracket "{" (stmtToDoc body) "}"
expToDoc JUndefined = text "null"
expToDoc (Index obj ix) = expToDoc obj ++ text "[" ++ expToDoc ix ++ text "]"
expToDoc (Dot obj nm) = expToDoc obj ++ text "." ++ jsIdent nm

caseBody : JSStmt e -> Doc
caseBody stmt@(JReturn x) = nest 2 (line ++ stmtToDoc stmt)
-- caseBody {e = Return} stmt@(JCase{}) = nest 2 (line ++ stmtToDoc stmt)
caseBody {e} stmt@(JCase{}) = nest 2 (line ++ stmtToDoc stmt </> text "break;")
caseBody stmt = line ++ text "{" ++ nest 2 (line ++ stmtToDoc stmt </> text "break;") </> text "}"

altToDoc : JAlt -> Doc
altToDoc (JConAlt nm stmt) = text "case" <+> text (quoteString nm) ++ text ":" ++ caseBody stmt
altToDoc (JDefAlt stmt) = text "default" ++ text ":" ++ caseBody stmt
altToDoc (JLitAlt a stmt) = text "case" <+> expToDoc a ++ text ":" ++ caseBody stmt

stmtToDoc (JSnoc x y) = stmtToDoc x </> stmtToDoc y
stmtToDoc (JPlain x) = expToDoc x ++ text ";"
-- I might not need these split yet.
stmtToDoc (JLet nm body) = text "let" <+> jsIdent nm ++ text ";" </> stmtToDoc body
stmtToDoc (JAssign nm expr) = jsIdent nm <+> text "=" <+> expToDoc expr ++ text ";"
stmtToDoc (JConst nm x) = text "const" <+> jsIdent nm <+> nest 2 (text "=" <+/> expToDoc x ++ text ";")
stmtToDoc (JReturn x) = text "return" <+> expToDoc x ++ text ";"
stmtToDoc (JError str) = text "throw new Error(" ++ text (quoteString str) ++ text ");"
stmtToDoc (JCase sc alts) =
  text "switch (" ++ expToDoc sc ++ text ")" <+> bracket "{" (stack $ map altToDoc alts) "}"

mkArgs : Nat -> List String -> List String
mkArgs Z acc = acc
mkArgs (S k) acc = mkArgs k ("h\{show k}" :: acc)

dcon : QName -> Nat -> Doc
dcon qn@(QN ns nm) Z = stmtToDoc $ JConst (show qn) $ LitObject [("tag", LitString nm)]
dcon qn@(QN ns nm) arity =
  let args := mkArgs arity []
      obj := ("tag", LitString nm) :: map (\x => (x, Var x)) args
  in stmtToDoc $ JConst (show qn) (JLam args (JReturn (LitObject obj)))

-- use iife to turn stmts into expr
maybeWrap : JSStmt Return -> JSExp
maybeWrap (JReturn exp) = exp
maybeWrap stmt = Apply (JLam [] stmt) []

entryToDoc : TopEntry -> M Doc
entryToDoc (MkEntry _ name ty (Fn tm)) = do
  debug "compileFun \{pprint [] tm}"
  ct <- compileFun tm
  let exp = maybeWrap $ termToJS empty ct JReturn
  pure $ text "const" <+> jsIdent (show name) <+> text "=" <+/> expToDoc exp ++ text ";"
entryToDoc (MkEntry _ name type Axiom) = pure $ text ""
entryToDoc (MkEntry _ name type (TCon strs)) = pure $ dcon name (piArity type)
entryToDoc (MkEntry _ name type (DCon arity str)) = pure $ dcon name arity
entryToDoc (MkEntry _ name type PrimTCon) = pure $ dcon name (piArity type)
entryToDoc (MkEntry _ name _ (PrimFn src _)) = pure $ text "const" <+> jsIdent (show name) <+> text "=" <+> text src

||| This version (call `reverse . snd <$> process "main" ([],[])`) will do dead
||| code elimination, but the Prelude js primitives are reaching for
||| stuff like True, False, MkUnit, fs which get eliminated
process : (List QName, List Doc) -> QName -> M (List QName, List Doc)
process (done,docs) nm = do
  let False = nm `elem` done | _ => pure (done,docs)
  top <- get
  case TopContext.lookup nm top of
    Nothing => error emptyFC "\{nm} not in scope"
    Just entry@(MkEntry _ name ty (PrimFn src uses)) => do
      (done,docs) <- foldlM assign (nm :: done, docs) uses
      pure (done, !(entryToDoc entry) :: docs)
    Just (MkEntry _ name ty (Fn tm)) => do
                debug "compileFun \{pprint [] tm}"
                ct <- compileFun tm
                -- If ct has zero arity and is a compount expression, this fails..
                let exp = maybeWrap $ termToJS empty ct JReturn
                let doc = text "const" <+> jsIdent (show name) <+> text "=" <+/> expToDoc exp ++ text ";"
                (done,docs) <- walkTm tm (nm :: done, docs)
                pure (done, doc :: docs)
    Just entry => pure (nm :: done, !(entryToDoc entry) :: docs)
  where
    assign : (List QName, List Doc) -> String -> M (List QName, List Doc)
    assign (done, docs) nm = case lookupRaw nm !get of
      Nothing => pure (done, docs)
      (Just (MkEntry fc name type def)) => do
        let tag = QN [] nm
        let False = tag `elem` done | _ => pure (done,docs)
        (done,docs) <- process (done, docs) name
        let doc = text "const" <+> jsIdent nm <+> text "=" <+> jsIdent (show name) ++ text ";"
        pure (tag :: done, doc :: docs)

    walkTm : Tm -> (List QName, List Doc) -> M (List QName, List Doc)
    walkAlt : (List QName, List Doc) -> CaseAlt -> M (List QName, List Doc)
    walkAlt acc (CaseDefault t) = walkTm t acc
    walkAlt acc (CaseCons name args t) = walkTm t acc
    walkAlt acc (CaseLit lit t) = walkTm t acc

    walkTm (Ref x nm y) acc = process acc nm
    walkTm (Lam x str _ _ t) acc = walkTm t acc
    walkTm (App x t u) acc = walkTm t !(walkTm u acc)
    walkTm (Pi x str icit y t u) acc = walkTm t !(walkTm u acc)
    walkTm (Let x str t u) acc = walkTm t !(walkTm u acc)
    walkTm (LetRec x str _ t u) acc = walkTm t !(walkTm u acc)
    walkTm (Case x t alts) acc = foldlM walkAlt acc alts
    walkTm _ acc = pure acc

export
compile : M (List Doc)
compile = do
  top <- get
  case lookupRaw "main" top of
    Just (MkEntry fc name type def) => do
      tmp <- snd <$> process ([],[]) name
      let exec = stmtToDoc $ JPlain $ Apply (Var $ show name) []
      pure $ reverse (exec :: tmp)
    -- If there is no main, compile everything for the benefit of the playground
    Nothing => do
      top <- get
      traverse entryToDoc $ map snd $ SortedMap.toList top.defs


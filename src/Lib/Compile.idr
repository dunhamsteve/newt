module Lib.Compile

import Lib.Types
import Lib.Prettier

-- return is in the wrong spot
-- case is still FIXME
-- case missing break

data Kind = Plain | Return | Assign String


data JSStmt : Kind -> Type

data JSExp : Type where
  LitArray : List JSExp -> JSExp
  LitObject : List (String, JSExp) -> JSExp
  LitString : String -> JSExp
  Apply : JSExp -> List JSExp -> JSExp
  Var : String -> JSExp
  JLam : String -> JSStmt Return -> JSExp
  JUndefined : JSExp
  Index : JSExp -> JSExp -> JSExp
  Dot : JSExp -> String -> JSExp

data JSStmt : Kind -> Type where
  -- Maybe make this a snoc...
  JSeq : JSStmt Plain -> JSStmt a -> JSStmt a
  JPlain : JSExp -> JSStmt Plain
  JConst : (nm : String) -> JSExp -> JSStmt Plain
  JReturn : JSExp -> JSStmt Return
  -- JAssign : (nm : String) -> JSExp -> JSStmt (Assign nm)
  -- TODO - switch to Nat tags
  JCase : JSExp -> List (String, JSStmt a) -> Maybe (JSStmt a) -> JSStmt a
  -- throw can't be used
  JError : String -> JSStmt a

Cont e = JSExp -> JSStmt e

-- This is inspired by A-normalization, look into the continuation monad
-- There is an index on JSStmt, adopted from Stefan's code.
--
-- Here we turn a Term into a statement (which may be a sequence of statements), there
-- is a continuation, which turns the final JSExpr into a JSStmt, and the function returns
-- a JSStmt, possibly wrapping recursive calls with JSeq
termToJS : List JSExp -> Tm -> Cont e -> JSStmt e
termToJS env (Bnd _ k) f = case getAt k env of
  (Just e) => f e
  Nothing => ?bad_bounds
termToJS env (Ref _ nm y) f = f $ Var nm
termToJS env (Meta _ k) f = f $ LitString "META \{show k}"
termToJS env (Lam _ nm t) f =
  let nm' = "nm$\{show $ length env}"
      env' = (Var nm' :: env)
  in f $ JLam nm' (termToJS env' t JReturn)
termToJS env (App _ t u) f = termToJS env t (\ t' => termToJS env u (\ u' => f (Apply t' [u'])))
termToJS env (U _) f = f $ LitString "U"
termToJS env (Pi _ nm icit t u) f = f $ LitString "Pi \{nm}"
termToJS env (Case _ t alts) f =
  -- need to assign the scrutinee to a variable
  -- and add (Bnd -> JSExpr map)
  termToJS env t (\ t' =>
    let (l,c) = getFC t in
    let nm = "sc$\{show l}$\{show c}" in
    JSeq (JConst nm t')
      (JCase (Dot (Var nm) "tag") (map (termToJSAlt nm) alts) Nothing))
  where
    -- Stuff nm.h1, nm.h2, ... into environment
    mkEnv : String -> Nat -> List JSExp -> List String -> List JSExp
    mkEnv nm k env [] = env
    mkEnv nm k env (x :: xs) = mkEnv nm (S k) (Dot (Var nm) "h\{show k}" :: env) xs

    termToJSAlt : String -> CaseAlt -> (String, JSStmt e)
    termToJSAlt nm (CaseDefault u) = ?handle_default_case
    termToJSAlt nm (CaseCons name args u) =
      let env' = mkEnv nm 0 env args in
      (name, termToJS env' u f)

-- FIXME escape
jsString : String -> Doc
jsString str = text "\"\{str}\""

stmtToDoc : JSStmt e -> Doc

expToDoc : JSExp -> Doc
expToDoc (LitArray xs) = ?expToDoc_rhs_0
expToDoc (LitObject xs) = ?expToDoc_rhs_1
expToDoc (LitString str) = jsString str
expToDoc (Apply x xs) = expToDoc x ++ "(" ++ spread (map expToDoc xs) ++ ")"
expToDoc (Var nm) = text nm
expToDoc (JLam nm (JReturn exp)) = text "(" <+> text nm <+> ") =>" <+> expToDoc exp
expToDoc (JLam nm body) = text "(" <+> text nm <+> ") =>" <+> bracket "{" (stmtToDoc body) "}"
expToDoc JUndefined = text "undefined"
expToDoc (Index obj ix) = expToDoc obj ++ "[" ++ expToDoc ix ++ "]"
expToDoc (Dot obj nm) = expToDoc obj ++ "." ++ text nm

altToDoc : (String, JSStmt e) -> Doc
-- line is an extra newline, but nest seems borken
altToDoc (nm, (JReturn exp)) = text "case" <+> jsString nm ++ ":" </> nest 2 (line ++ "return" <+> expToDoc exp)
altToDoc (nm, stmt) = text "case" <+> jsString nm ++ ":" </> nest 2 (line ++ stmtToDoc stmt </> text "break;")


stmtToDoc (JSeq x y) = stmtToDoc x </> stmtToDoc y
stmtToDoc (JPlain x) = expToDoc x
stmtToDoc (JConst nm x) = text "const" <+> text nm <+> "=" <+/> expToDoc x
stmtToDoc (JReturn x) = text "return" <+> expToDoc x
stmtToDoc (JError str) = text "throw new Error(" ++ text str ++ ")"
stmtToDoc (JCase sc alts y) =
  text "switch (" ++ expToDoc sc ++ ")" <+> bracket "{" (stack $ map altToDoc alts) "}"

function : String -> Tm -> Doc
function nm tm =
  let body = stmtToDoc $ termToJS [] tm JReturn in
  text "const" <+> text nm <+> "=" <+/> body

entryToDoc : TopEntry -> Maybe Doc
entryToDoc (MkEntry name type (Fn tm)) =
  let body = stmtToDoc $ termToJS [] tm JPlain in
  Just (text "const" <+> text name <+> "=" <+/> body)
entryToDoc (MkEntry name type Axiom) = Nothing
entryToDoc (MkEntry name type (TCon strs)) = Nothing
entryToDoc (MkEntry name type (DCon k str)) = Nothing

export
compile : M Doc
compile = do
  top <- get
  pure $ stack $ mapMaybe entryToDoc top.defs

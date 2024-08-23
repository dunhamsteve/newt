-- TODO I think I'm missing the bit where a case might need to be assigned to a variable.
-- TODO And then get primitives and a way to declare extern functions.  That may get us
-- to utility
module Lib.Compile

import Lib.Types
import Lib.Prettier
import Lib.CompileExp
import Data.String

data Kind = Plain | Return | Assign String

data JSStmt : Kind -> Type

data JAlt : Type where
  JConAlt : String -> JSStmt e -> JAlt
  JDefAlt : JSStmt e -> JAlt

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
  -- JAssign : (nm : String) -> JSExp -> JSStmt (Assign nm)
  -- TODO - switch to Nat tags
  -- FIXME add e to JAlt (or just drop it?)
  JCase : JSExp -> List JAlt -> JSStmt a
  -- throw can't be used
  JError : String -> JSStmt a

Cont e = JSExp -> JSStmt e

||| JSEnv contains `Var` for binders or `Dot` for destructured data. It
||| used to translate binders
JSEnv : Type
JSEnv = List JSExp

-- Stuff nm.h1, nm.h2, ... into environment
mkEnv : String -> Nat -> List JSExp -> List String -> List JSExp
mkEnv nm k env [] = env
mkEnv nm k env (x :: xs) = mkEnv nm (S k) (Dot (Var nm) "h\{show k}" :: env) xs

envNames : Env -> List String

-- If I was golfing, I'd be tempted to stick with deBruijn

||| given a name, find a similar one that doesn't shadow in Env
fresh : String -> JSEnv -> String
fresh nm env = if free env nm then nm else go nm 1
  where
    free : JSEnv -> String -> Bool
    free [] nm = True
    free (Var n :: xs) nm = if n == nm then False else free xs nm
    free (_ :: xs) nm = free xs nm

    go : String -> Nat -> String
    go nm k = let nm' = "\{nm}\{show k}" in if free env nm' then nm' else go nm (S k)

-- This is inspired by A-normalization, look into the continuation monad
-- There is an index on JSStmt, adopted from Stefan Hoeck's code.
--
-- Here we turn a Term into a statement (which may be a sequence of statements), there
-- is a continuation, which turns the final JSExpr into a JSStmt, and the function returns
-- a JSStmt, wrapping recursive calls in JSnoc if necessary.
termToJS : List JSExp -> CExp -> Cont e -> JSStmt e
termToJS env (CBnd k) f = case getAt k env of
  (Just e) => f e
  Nothing => ?bad_bounds
termToJS env (CLam nm t) f =
  let nm' = fresh nm env -- "\{nm}$\{show $ length env}"
      env' = (Var nm' :: env)
  in f $ JLam [nm'] (termToJS env' t JReturn)
termToJS env (CFun nms t) f =
  let nms' = map (\nm => fresh nm env) nms
      env' = foldl (\ e, nm => Var nm :: e) env nms'
  in f $ JLam nms' (termToJS env' t JReturn)
termToJS env (CRef nm) f = f $ Var nm
termToJS env (CMeta k) f = f $ LitString "META \{show k}"
termToJS env (CLit (LString str)) f = f (LitString str)
termToJS env (CLit (LInt i)) f = f (LitInt i)
termToJS env (CApp t args) f = termToJS env t (\ t' => argsToJS args [<] (\ args' => f (Apply t' args')))
  where
    argsToJS : List CExp -> SnocList JSExp -> (List JSExp -> JSStmt e) -> JSStmt e
    argsToJS [] acc k = k (acc <>> [])
    argsToJS (x :: xs) acc k = termToJS env x (\ x' => argsToJS xs (acc :< x') k)


termToJS env (CCase t alts) f =
  -- need to assign the scrutinee to a variable (unless it is a var already?)
  -- and add (Bnd -> JSExpr map)
  -- TODO default case, let's drop the extra field.

  termToJS env t $ \case
    (Var nm) => (JCase (Dot (Var nm) "tag") (map (termToJSAlt nm) alts))
    t' =>
      let nm = fresh "sc" env in
        JSnoc (JConst nm t')
          (JCase (Dot (Var nm) "tag") (map (termToJSAlt nm) alts))
  where
    termToJSAlt : String -> CAlt -> JAlt
    termToJSAlt nm (CConAlt name args u) = JConAlt name (termToJS (mkEnv nm 0 env args) u f)
    -- intentially reusing scrutinee name here
    termToJSAlt nm (CDefAlt u) = JDefAlt (termToJS (Var nm :: env) u f)
    label : JSExp -> (String -> JSStmt e) -> JSStmt e
    label (Var nm) f = f nm
    label t f = ?label_rhs


-- FIXME escape
jsString : String -> Doc
jsString str = text "\"\{str}\""

stmtToDoc : JSStmt e -> Doc

||| separate with space
export
commaSep : List Doc -> Doc
commaSep = folddoc (\a, b => a ++ "," <+> b)

expToDoc : JSExp -> Doc
expToDoc (LitArray xs) = ?expToDoc_rhs_0
expToDoc (LitObject xs) = text "{" <+> folddoc (\ a, e => a ++ ", " <+/> e) (map entry xs) <+> text "}"
  where
    entry : (String, JSExp) -> Doc
    -- TODO quote if needed
    entry (nm, exp) = text nm ++ ":" <+> expToDoc exp

expToDoc (LitString str) = jsString str
expToDoc (LitInt i) = text $ show i
expToDoc (Apply x xs) = expToDoc x ++ "(" ++ commaSep (map expToDoc xs) ++ ")"
expToDoc (Var nm) = text nm
expToDoc (JLam nms (JReturn exp)) = text "(" <+> text (joinBy ", " nms) <+> ") =>" <+> expToDoc exp
expToDoc (JLam nms body) = text "(" <+> text (joinBy ", " nms) <+> ") =>" <+> bracket "{" (stmtToDoc body) "}"
expToDoc JUndefined = text "undefined"
expToDoc (Index obj ix) = expToDoc obj ++ "[" ++ expToDoc ix ++ "]"
expToDoc (Dot obj nm) = expToDoc obj ++ "." ++ text nm

caseBody : JSStmt e -> Doc
caseBody stmt@(JReturn x) = nest 2 (line ++ stmtToDoc stmt)
caseBody stmt = nest 2 (line ++ stmtToDoc stmt </> text "break;")

altToDoc : JAlt -> Doc
altToDoc (JConAlt nm stmt) = text "case" <+> jsString nm ++ ":" ++ caseBody stmt
altToDoc (JDefAlt stmt) = text "default" ++ ":" ++ caseBody stmt

stmtToDoc (JSnoc x y) = stmtToDoc x </> stmtToDoc y
stmtToDoc (JPlain x) = expToDoc x ++ ";"
stmtToDoc (JConst nm x) = text "const" <+> text nm <+> "=" <+/> expToDoc x ++ ";"
stmtToDoc (JReturn x) = text "return" <+> expToDoc x ++ ";"
stmtToDoc (JError str) = text "throw new Error(" ++ text str ++ ");"
stmtToDoc (JCase sc alts) =
  text "switch (" ++ expToDoc sc ++ ")" <+> bracket "{" (stack $ map altToDoc alts) "}"

mkArgs : Nat -> List String -> List String
mkArgs Z acc = acc
mkArgs (S k) acc = mkArgs k ("h\{show k}" :: acc)

dcon : String -> Nat -> Doc
dcon nm arity =
  let args := mkArgs arity []
      obj := ("tag", LitString nm) :: map (\x => (x, Var x)) args
  in stmtToDoc $ JConst nm (JLam args (JReturn (LitObject obj)))


entryToDoc : TopEntry -> M Doc
entryToDoc (MkEntry name ty (Fn tm)) = do
  -- so this has a bunch of lambdas on it now, which we want to consolidate
  -- and we might need betas? It seems like a mirror of what happens in CExp
  ct <- compileFun tm
  let body = stmtToDoc $ termToJS [] ct JPlain
  pure (text "const" <+> text name <+> text "=" <+/> body)
entryToDoc (MkEntry name type Axiom) = pure ""
entryToDoc (MkEntry name type (TCon strs)) = pure ""
entryToDoc (MkEntry name type (DCon arity str)) = pure $ dcon name arity
entryToDoc (MkEntry name _ PrimTCon) = pure $ text "/* PrimTCon \{name} */"
entryToDoc (MkEntry name _ (PrimFn src)) = pure $ text "const" <+> text name <+> "=" <+> text src

export
compile : M Doc
compile = do
  top <- get
  pure $ stack $ !(traverse entryToDoc top.defs)

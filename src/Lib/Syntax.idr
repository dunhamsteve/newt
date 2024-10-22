module Lib.Syntax

import Data.String
import Data.Maybe
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types

public export
data Raw : Type where

public export
data RigCount = Rig0 | RigW

public export
data Pattern
  = PatVar FC Icit Name
  | PatCon FC Icit Name (List Pattern)
  | PatWild FC Icit
  -- Not handling this yet, but we need to be able to work with numbers and strings...
  | PatLit FC Literal

export
getIcit : Pattern -> Icit
getIcit (PatVar x icit str) = icit
getIcit (PatCon x icit str xs) = icit
getIcit (PatWild x icit) = icit
getIcit (PatLit fc lit) = Explicit


export
HasFC Pattern where
  getFC (PatVar fc _ _) = fc
  getFC (PatCon fc _ _ _) = fc
  getFC (PatWild fc _) = fc
  getFC (PatLit fc lit) = fc

-- %runElab deriveShow `{Pattern}
public export
Constraint : Type
Constraint = (String, Pattern)

public export
record Clause where
  constructor MkClause
  fc : FC
  -- I'm including the type of the left, so we can check pats and get the list of possibilities
  -- But maybe rethink what happens on the left.
  -- It's a VVar k or possibly a pattern.
  -- a pattern either is zipped out, dropped (non-match) or is assigned to rhs
  -- if we can do all three then we can have a VVar here.
  cons : List Constraint
  pats : List Pattern
  -- We'll need some context to typecheck this
  -- it has names from Pats, which will need types in the env
  expr : Raw

-- could be a pair, but I suspect stuff will be added?
public export
data RCaseAlt = MkAlt Raw Raw

data Raw : Type where
  RVar : FC -> (nm : Name) -> Raw
  RLam : FC -> (nm : String) -> (icit : Icit) -> (ty : Raw) -> Raw
  RApp : FC -> (t : Raw) -> (u : Raw) -> (icit : Icit) -> Raw
  RU   : FC -> Raw
  RPi  : FC -> (nm : Maybe Name) -> (icit : Icit) -> (ty : Raw) -> (sc : Raw) -> Raw
  RLet : FC -> (nm : Name) -> (ty : Raw) -> (v : Raw) -> (sc : Raw) -> Raw
  RAnn  : FC -> (tm : Raw) -> (ty : Raw) -> Raw
  RLit : FC -> Literal -> Raw
  RCase : FC -> (scrut : Raw) -> (alts : List RCaseAlt) -> Raw
  RImplicit : FC -> Raw
  RHole : FC -> Raw
  -- not used, but intended to allow error recovery
  RParseError : FC -> String -> Raw

%name Raw tm

export
HasFC Raw where
  getFC (RVar fc nm) = fc
  getFC (RLam fc nm icit ty) = fc
  getFC (RApp fc t u icit) = fc
  getFC (RU fc) = fc
  getFC (RPi fc nm icit ty sc) = fc
  getFC (RLet fc nm ty v sc) = fc
  getFC (RAnn fc tm ty) = fc
  getFC (RLit fc y) = fc
  getFC (RCase fc scrut alts) = fc
  getFC (RImplicit fc) = fc
  getFC (RHole fc) = fc
  getFC (RParseError fc str) = fc
-- derive some stuff - I'd like json, eq, show, ...



public export
data Import = MkImport FC Name

-- FIXME - I think I don't want "where" here, but the parser has an issue
public export
data Decl
  = TypeSig FC Name Raw
  | Def FC Name (List (Raw,Raw)) -- (List Clause)
  | DCheck FC Raw Raw
  | Data FC Name Raw (List Decl)
  | PType FC Name (Maybe Raw)
  | PFunc FC Name Raw String
  | PMixFix FC Name Nat Fixity


public export
record Module where
  constructor MkModule
  name : Name
  imports : List Import
  decls : List Decl

foo : List String -> String
foo ts = "(" ++ unwords ts ++ ")"

-- Show Literal where
--   show (LString str) = foo [ "LString", show str]
--   show (LInt i) = foo [ "LInt", show i]
--   show (LChar c) = foo [ "LChar", show c]

export
covering
implementation Show Raw

export
implementation Show Decl

export Show Pattern

export covering
Show Clause where
  show (MkClause fc cons pats expr) = show (fc, cons, pats, expr)

Show Import where
  show (MkImport _ str) = foo ["MkImport", show str]

covering
Show Decl where
  show (TypeSig _ str x) = foo ["TypeSig", show str, show x]
  show (Def _ str clauses) = foo ["Def", show str, show clauses]
  show (Data _ str xs ys) = foo ["Data", show str, show xs, show ys]
  show (DCheck _ x y) = foo ["DCheck", show x, show y]
  show (PType _ name ty) = foo ["PType", name, show ty]
  show (PFunc _ nm ty src) = foo ["PFunc", nm, show ty, show src]
  show (PMixFix _ nm prec fix) = foo ["PMixFix", nm, show prec, show fix]

export covering
Show Module where
  show (MkModule name imports decls) = foo ["MkModule", show name, show imports, show decls]

Show RigCount where
  show Rig0 = "Rig0"
  show RigW = "RigW"

export
Show Pattern where
  show (PatVar _ icit str) = foo ["PatVar", show icit, show str]
  show (PatCon _ icit str xs) = foo ["PatCon", show icit, show str, assert_total $ show xs]
  show (PatWild _ icit) = foo ["PatWild", show icit]
  show (PatLit _ lit) = foo ["PatLit", show lit]

covering
Show RCaseAlt where
  show (MkAlt x y)= foo ["MkAlt", show x, assert_total $ show y]

covering
Show Raw where
  show (RImplicit _) = "_"
  show (RHole _) = "?"
  show (RVar _ name) = foo ["RVar", show name]
  show (RAnn _ t ty) = foo [ "RAnn", show t, show ty]
  show (RLit _ x) = foo [ "RLit", show x]
  show (RLet _ x ty v scope) = foo [ "Let", show x, " : ", show ty, " = ", show v, " in ", show scope]
  show (RPi _ str x y z) = foo [ "Pi", show str, show x, show y, show z]
  show (RApp _ x y z) = foo [ "App", show x, show y, show z]
  show (RLam _ x i y) = foo [ "Lam", show x, show i, show y]
  show (RCase _ x xs) = foo [ "Case", show x, show xs]
  show (RParseError _ str) = foo [ "ParseError", "str"]
  show (RU _) = "U"

export
Pretty Literal where
  pretty (LString str) = text $ interpolate str
  pretty (LInt i) = text $ show i
  pretty (LChar c) = text $ show c

export
Pretty Pattern where
  -- FIXME - wrap Implicit with {}
  pretty (PatVar _ icit nm) = text nm
  pretty (PatCon _ icit nm args) = text nm <+> spread (map pretty args)
  pretty (PatWild _icit) = "_"
  pretty (PatLit _ lit) = pretty lit



export
Pretty Raw where
  pretty = asDoc 0
    where
    wrap : Icit -> Doc -> Doc
    wrap Explicit x = x
    wrap Implicit x = text "{" ++ x ++ text "}"

    par : Nat -> Nat -> Doc -> Doc
    par p p' d = if p' < p then text "(" ++ d ++ text ")" else d

    asDoc : Nat -> Raw -> Doc
    asDoc p (RVar _ str) = text str
    asDoc p (RLam _ str icit x) = par p 0 $ text "\\" ++ wrap icit (text str) <+> text "=>" <+> asDoc 0 x
    -- This needs precedence and operators...
    asDoc p (RApp _ x y Explicit) = par p 2 $ asDoc 2 x <+> asDoc 3 y
    asDoc p (RApp _ x y Implicit) = par p 2 $ asDoc 2 x <+> text "{" ++ asDoc 0 y ++ text "}"
    asDoc p (RU _) = text "U"
    asDoc p (RPi _ Nothing Explicit ty scope) = par p 1 $ asDoc p ty <+> text "->" <+/> asDoc p scope
    asDoc p (RPi _ (Just x) Explicit ty scope) =
      par p 1 $ text "(" <+> text x <+> text ":" <+> asDoc p ty <+> text ")" <+> text "->" <+/> asDoc p scope
    asDoc p (RPi _ nm Implicit ty scope) =
      par p 1 $ text "{" <+> text (fromMaybe "_" nm) <+> text ":" <+> asDoc p ty <+> text "}" <+> text "->" <+/> asDoc 1 scope
    asDoc p (RLet _ x v ty scope) =
      par p 0 $ text "let" <+> text x <+> text ":" <+> asDoc p ty
          <+> text "=" <+> asDoc p v
          <+/> text "in" <+> asDoc p scope
    -- does this exist?
    asDoc p (RAnn _ x y) = text "TODO - RAnn"
    asDoc p (RLit _ lit) = pretty lit
    asDoc p (RCase _ x xs) = text "TODO - RCase"
    asDoc p (RImplicit _) = text "_"
    asDoc p (RHole _) = text "?"
    asDoc p (RParseError _ str) = text "ParseError \{str}"

export
Pretty Module where
  pretty (MkModule name imports decls) =
    text "module" <+> text name
      </> stack (map doImport imports)
      </> stack (map doDecl decls)
      where
        doImport : Import -> Doc
        doImport (MkImport _ nm) = text "import" <+> text nm ++ line

        doDecl : Decl -> Doc
        doDecl (TypeSig _ nm ty) = text nm <+> text ":" <+> nest 2 (pretty ty)
        doDecl (Def _ nm clauses) = stack $ map (\(a,b) => pretty a <+> "=" <+> pretty b) clauses
        -- the behavior of nest is kinda weird, I have to do the nest before/around the </>.
        doDecl (Data _ nm x xs) = text "data" <+> text nm <+> text ":" <+>  pretty x <+> (nest 2 $ text "where" </> stack (map doDecl xs))
        doDecl (DCheck _ x y) = text "#check" <+> pretty x <+> ":" <+> pretty y
        doDecl (PType _ nm ty) = text "ptype" <+> text nm <+> (maybe empty (\ty => ":" <+> pretty ty) ty)
        doDecl (PFunc _ nm ty src) = "pfunc" <+> text nm <+> ":" <+> nest 2 (pretty ty <+> ":=" <+/> text (show src))
        doDecl (PMixFix _ _ _ fix) = text (show fix)

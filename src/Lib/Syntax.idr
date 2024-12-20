module Lib.Syntax

import Data.String
import Data.Maybe
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types

public export
data Raw : Type where

public export
data Pattern
  = PatVar FC Icit Name
  | PatCon FC Icit Name (List Pattern) (Maybe Name)
  | PatWild FC Icit
  -- Not handling this yet, but we need to be able to work with numbers and strings...
  | PatLit FC Literal

export
getIcit : Pattern -> Icit
getIcit (PatVar x icit str) = icit
getIcit (PatCon x icit str xs as) = icit
getIcit (PatWild x icit) = icit
getIcit (PatLit fc lit) = Explicit


export
HasFC Pattern where
  getFC (PatVar fc _ _) = fc
  getFC (PatCon fc _ _ _ _) = fc
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

public export
data DoStmt : Type where
  DoExpr : (fc : FC) -> Raw -> DoStmt
  DoLet : (fc : FC) -> String -> Raw -> DoStmt
  DoArrow : (fc: FC) -> Raw -> Raw -> List RCaseAlt -> DoStmt

data Decl : Type
data Raw : Type where
  RVar : (fc : FC) -> (nm : Name) -> Raw
  RLam : (fc : FC) -> BindInfo -> (ty : Raw) -> Raw
  RApp : (fc : FC) -> (t : Raw) -> (u : Raw) -> (icit : Icit) -> Raw
  RU   : (fc : FC) -> Raw
  RPi  : (fc : FC) -> BindInfo -> (ty : Raw) -> (sc : Raw) -> Raw
  RLet : (fc : FC) -> (nm : Name) -> (ty : Raw) -> (v : Raw) -> (sc : Raw) -> Raw
  RAnn : (fc : FC) -> (tm : Raw) -> (ty : Raw) -> Raw
  RLit : (fc : FC) -> Literal -> Raw
  RCase : (fc : FC) -> (scrut : Raw) -> (alts : List RCaseAlt) -> Raw
  RImplicit : (fc : FC) -> Raw
  RHole : (fc : FC) -> Raw
  RDo : (fc : FC) -> List DoStmt -> Raw
  RIf : (fc : FC) -> Raw -> Raw -> Raw -> Raw
  RWhere : (fc : FC) -> (List Decl) -> Raw -> Raw
  RAs : (fc : FC) -> Name -> Raw -> Raw

%name Raw tm


export
HasFC Raw where
  getFC (RVar fc nm) = fc
  getFC (RLam fc _ ty) = fc
  getFC (RApp fc t u icit) = fc
  getFC (RU fc) = fc
  getFC (RPi fc _ ty sc) = fc
  getFC (RLet fc nm ty v sc) = fc
  getFC (RAnn fc tm ty) = fc
  getFC (RLit fc y) = fc
  getFC (RCase fc scrut alts) = fc
  getFC (RImplicit fc) = fc
  getFC (RHole fc) = fc
  getFC (RDo fc stmts) = fc
  getFC (RIf fc _ _ _) = fc
  getFC (RWhere fc _ _) = fc
  getFC (RAs fc _ _) = fc


-- derive some stuff - I'd like json, eq, show, ...



public export
data Import = MkImport FC Name


public export
Telescope : Type
Telescope = List (BindInfo, Raw)

public export
data Decl
  = TypeSig FC (List Name) Raw
  | Def FC Name (List (Raw, Raw)) -- (List Clause)
  | DCheck FC Raw Raw
  | Data FC Name Raw (List Decl)
  | PType FC Name (Maybe Raw)
  | PFunc FC Name (List String) Raw String
  | PMixFix FC (List Name) Nat Fixity
  | Class FC Name Telescope (List Decl)
  | Instance FC Raw (List Decl)
  | Record FC Name Telescope (Maybe Name) (List Decl)

public export
HasFC Decl where
  getFC (TypeSig x strs tm) = x
  getFC (Def x str xs) = x
  getFC (DCheck x tm tm1) = x
  getFC (Data x str tm xs) = x
  getFC (PType x str mtm) = x
  getFC (PFunc x str _ tm str1) = x
  getFC (PMixFix x strs k y) = x
  getFC (Class x str xs ys) = x
  getFC (Instance x tm xs) = x
  getFC (Record x str tm str1 xs) = x

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

Show BindInfo where
  show (BI _ nm icit quant) = foo ["BI", show nm, show icit, show quant]

-- this is for debugging, use pretty when possible
covering
Show Decl where
  show (TypeSig _ str x) = foo ["TypeSig", show str, show x]
  show (Def _ str clauses) = foo ["Def", show str, show clauses]
  show (Data _ str xs ys) = foo ["Data", show str, show xs, show ys]
  show (DCheck _ x y) = foo ["DCheck", show x, show y]
  show (PType _ name ty) = foo ["PType", name, show ty]
  show (PFunc _ nm uses ty src) = foo ["PFunc", nm, show uses, show ty, show src]
  show (PMixFix _ nms prec fix) = foo ["PMixFix", show nms, show prec, show fix]
  show (Class _ nm tele decls) = foo ["Class",  nm, "...", show $ map show decls]
  show (Instance _ nm decls) = foo ["Instance",  show nm, show $ map show decls]
  show (Record _ nm tele nm1 decls) = foo ["Record", show nm, show tele, show nm1, show decls]

export covering
Show Module where
  show (MkModule name imports decls) = foo ["MkModule", show name, show imports, show decls]

export
Show Pattern where
  show (PatVar _ icit str) = foo ["PatVar", show icit, show str]
  show (PatCon _ icit str xs as) = foo ["PatCon", show icit, show str, assert_total $ show xs, show as]
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
  show (RPi _ bi y z) = foo [ "Pi", show bi, show y, show z]
  show (RApp _ x y z) = foo [ "App", show x, show y, show z]
  show (RLam _ bi y) = foo [ "Lam", show bi, show y]
  show (RCase _ x xs) = foo [ "Case", show x, show xs]
  show (RDo _ stmts) = foo [ "DO", "FIXME"]
  show (RU _) = "U"
  show (RIf _ x y z) = foo [ "If", show x, show y, show z]
  show (RWhere _ _ _) = foo [ "Where", "FIXME"]
  show (RAs _ nm x) = foo [ "RAs", nm, show x]

export
Pretty Literal where
  pretty (LString str) = text $ interpolate str
  pretty (LInt i) = text $ show i
  pretty (LChar c) = text $ show c

export
Pretty Pattern where
  -- FIXME - wrap Implicit with {}
  pretty (PatVar _ icit nm) = text nm
  pretty (PatCon _ icit nm args Nothing) = text nm <+> spread (map pretty args)
  pretty (PatCon _ icit nm args (Just as)) = text as ++ "@(" ++ text nm <+> spread (map pretty args) ++ ")"
  pretty (PatWild _icit) = "_"
  pretty (PatLit _ lit) = pretty lit

wrap : Icit -> Doc -> Doc
wrap Explicit x = text "(" ++ x ++ text ")"
wrap Implicit x = text "{" ++ x ++ text "}"
wrap Auto x = text "{{" ++ x ++ text "}}"

export
Pretty Raw where
  pretty = asDoc 0
    where
    bindDoc : BindInfo -> Doc
    bindDoc (BI _ nm icit quant) = ?rhs_0

    par : Nat -> Nat -> Doc -> Doc
    par p p' d = if p' < p then text "(" ++ d ++ text ")" else d

    asDoc : Nat -> Raw -> Doc
    asDoc p (RVar _ str) = text str
    asDoc p (RLam _ (BI _ nm icit q) x) = par p 0 $ text "\\" ++ wrap icit (text nm) <+> text "=>" <+> asDoc 0 x
    -- This needs precedence and operators...
    asDoc p (RApp _ x y Explicit) = par p 2 $ asDoc 2 x <+> asDoc 3 y
    asDoc p (RApp _ x y Implicit) = par p 2 $ asDoc 2 x <+> text "{" ++ asDoc 0 y ++ text "}"
    asDoc p (RApp _ x y Auto) = par p 2 $ asDoc 2 x <+> text "{{" ++ asDoc 0 y ++ text "}}"
    asDoc p (RU _) = text "U"
    asDoc p (RPi _ (BI _ "_" Explicit Many) ty scope) = par p 1 $ asDoc p ty <+> text "->" <+/> asDoc p scope
    asDoc p (RPi _ (BI _ nm icit quant) ty scope) =
      par p 1 $ wrap icit (text (show quant ++ nm) <+> text ":" <+> asDoc p ty ) <+> text "->" <+/> asDoc 1 scope
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
    asDoc p (RDo _ stmts) = text "TODO - RDo"
    asDoc p (RIf _ x y z) = par p 0 $ text "if" <+> asDoc 0 x <+/> "then" <+> asDoc 0 y <+/> "else" <+> asDoc 0 z
    asDoc p (RWhere _ dd b) = text "TODO pretty where"
    asDoc p (RAs _ nm x) = text nm ++ "@(" ++ asDoc 0 x ++ ")"

prettyBind : (BindInfo, Raw) -> Doc
prettyBind (BI _ nm icit quant, ty) = wrap icit (text (show quant ++ nm) <+> text ":" <+> pretty ty)

export
Pretty Decl where
  pretty (TypeSig _ nm ty) = spread (map text nm) <+> text ":" <+> nest 2 (pretty ty)
  pretty (Def _ nm clauses) = stack $ map (\(a,b) => pretty a <+> "=" <+> pretty b) clauses
  pretty (Data _ nm x xs) = text "data" <+> text nm <+> text ":" <+>  pretty x <+> (nest 2 $ text "where" </> stack (map pretty xs))
  pretty (DCheck _ x y) = text "#check" <+> pretty x <+> ":" <+> pretty y
  pretty (PType _ nm ty) = text "ptype" <+> text nm <+> (maybe empty (\ty => ":" <+> pretty ty) ty)
  pretty (PFunc _ nm [] ty src) = "pfunc" <+> text nm <+> ":" <+> nest 2 (pretty ty <+> ":=" <+/> text (show src))
  pretty (PFunc _ nm uses ty src) = "pfunc" <+> text nm <+> "uses" <+> spread (map text uses) <+> ":" <+> nest 2 (pretty ty <+> ":=" <+/> text (show src))
  pretty (PMixFix _ names prec fix) = text (show fix) <+> text (show prec) <+> spread (map text names)
  pretty (Record _ nm tele cname decls) = text "record" <+> text nm <+> ":" <+> spread (map prettyBind tele)
    <+> (nest 2 $ text "where" </> stack (maybe empty (\ nm' => text "constructor" <+> text nm') cname :: map pretty decls))
  pretty (Class _ nm tele decls) = text "class" <+> text nm <+> ":" <+> spread (map prettyBind tele)
    <+> (nest 2 $ text "where" </> stack (map pretty decls))
  pretty (Instance _ _ _) = text "TODO pretty Instance"

export
Pretty Module where
  pretty (MkModule name imports decls) =
    text "module" <+> text name
      </> stack (map doImport imports)
      </> stack (map pretty decls)
      where
        doImport : Import -> Doc
        doImport (MkImport _ nm) = text "import" <+> text nm ++ line


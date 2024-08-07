module Lib.Syntax

import Data.String
import Data.Maybe
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types

public export
data Raw : Type where

public export
data Literal = LString String | LInt Int | LBool Bool
public export
data RigCount = Rig0 | RigW

public export
data Pattern
  = PatVar Name
  | PatCon Name (List (Pattern, RigCount))
  | PatWild
  | PatLit Literal

-- %runElab deriveShow `{Pattern}

-- could be a pair, but I suspect stuff will be added?
public export
data RCaseAlt = MkAlt Raw Raw

-- FC = MkPair Int Int


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
getFC : Raw -> FC
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

-- FIXME - I think I don't want "where" here, but the parser has an issue
public export
data Decl : Type where

Telescope: Type
Telescope = List Decl -- pi-forall, always typeSig?

data ConstrDef = MkCDef Name Telescope

data Decl
  = TypeSig FC Name Raw
  | Def FC Name Raw
  | DImport FC Name
  | DCheck FC Raw Raw
  | Data FC Name Raw (List Decl)

public export
record Module where
  constructor MkModule
  name : Name
  decls : List Decl

foo : List String -> String
foo ts = "(" ++ unwords ts ++ ")"


Show Literal where
  show (LString str) = foo [ "LString", show str]
  show (LInt i) = foo [ "LInt", show i]
  show (LBool x) = foo [ "LBool", show x]


export
covering
implementation Show Raw

export
implementation Show Decl

covering
Show ConstrDef where
  show (MkCDef str xs) = foo ["MkCDef", show str, show xs]


covering
Show Decl where
  show (TypeSig _ str x) = foo ["TypeSig", show str, show x]
  show (Def _ str x) = foo ["Def", show str, show x]
  show (Data _ str xs ys) = foo ["Data", show str, show xs, show ys]
  show (DImport _ str) = foo ["DImport", show str]
  show (DCheck _ x y) = foo ["DCheck", show x, show y]

export covering
Show Module where
  show (MkModule name decls) = foo ["MkModule", show name, show decls]

Show RigCount where
  show Rig0 = "Rig0"
  show RigW = "RigW"

Show Pattern where
  show (PatVar str) = foo ["PatVar", show str]
  show (PatCon str xs) = foo ["PatCon", show str, assert_total $ show xs]
  show PatWild = "PatWild"
  show (PatLit x) = foo ["PatLit" , show x]

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
    asDoc p (RLit _ (LString str)) = text $ interpolate str
    asDoc p (RLit _ (LInt i)) = text $ show i
    asDoc p (RLit _ (LBool x)) = text $ show x
    asDoc p (RCase _ x xs) = text "TODO - RCase"
    asDoc p (RImplicit _) = text "_"
    asDoc p (RHole _) = text "?"
    asDoc p (RParseError _ str) = text "ParseError \{str}"

export
Pretty Module where
  pretty (MkModule name decls) =
    text "module" <+> text name </> stack (map doDecl decls)
      where
        doDecl : Decl -> Doc
        doDecl (TypeSig _ nm ty) = text nm <+> text ":" <+> nest 2 (pretty ty)
        doDecl (Def _ nm tm) = text nm <+> text "=" <+> nest 2 (pretty tm)
        doDecl (DImport _ nm) = text "import" <+> text nm ++ line
        -- the behavior of nest is kinda weird, I have to do the nest before/around the </>.
        doDecl (Data _ nm x xs) = text "data" <+> text nm <+> text ":" <+>  pretty x <+> (nest 2 $ text "where" </> stack (map doDecl xs))
        doDecl (DCheck _ x y) = text "#check" <+> pretty x <+> ":" <+> pretty y

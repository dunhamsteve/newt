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
data CaseAlt = MkAlt Raw Raw

data Raw : Type where
  RVar : (nm : Name) -> Raw
  RLam : (nm : String) -> (icit : Icit) -> (ty : Raw) -> Raw
  RApp : (t : Raw) -> (u : Raw) -> (icit : Icit) -> Raw
  RU   : Raw
  RPi  : (nm : Maybe Name) -> (icit : Icit) -> (ty : Raw) -> (sc : Raw) -> Raw
  RLet : (nm : Name) -> (ty : Raw) -> (v : Raw) -> (sc : Raw) -> Raw
  -- REVIEW do we want positions on terms?
  RSrcPos : SourcePos -> Raw -> Raw
  RAnn  : (tm : Raw) -> (ty : Raw) -> Raw
  RLit : Literal -> Raw
  RCase : (scrut : Raw) -> (alts : List CaseAlt) -> Raw
  RImplicit : Raw
  RHole : Raw
  -- not used, but intended to allow error recovery
  RParseError : String -> Raw

%name Raw tm

-- derive some stuff - I'd like json, eq, show, ...

public export
data Decl : Type where

Telescope: Type
Telescope = List Decl -- pi-forall, always typeSig?

data ConstrDef = MkCDef Name Telescope

data Decl
  = TypeSig Name Raw
  | Def Name Raw
  | DImport Name
  | DCheck Raw Raw
  | Data Name Raw (List Decl)

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
  show (TypeSig str x) = foo ["TypeSig", show str, show x]
  show (Def str x) = foo ["Def", show str, show x]
  show (Data str xs ys) = foo ["Data", show str, show xs, show ys]
  show (DImport str) = foo ["DImport", show str]
  show (DCheck x y) = foo ["DCheck", show x, show y]

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
Show CaseAlt where
  show (MkAlt x y)= foo ["MkAlt", show x, assert_total $ show y]

covering
Show Raw where
  show RImplicit = "_"
  show RHole = "?"
  show (RVar name) = foo ["RVar", show name]
  show (RAnn t ty) = foo [ "RAnn", show t, show ty]
  show (RLit x) = foo [ "RLit", show x]
  show (RLet x ty v scope) = foo [ "Let", show x, " : ", show ty, " = ", show v, " in ", show scope]
  show (RPi str x y z) = foo [ "Pi", show str, show x, show y, show z]
  show (RApp x y z) = foo [ "App", show x, show y, show z]
  show (RLam x i y) = foo [ "Lam", show x, show i, show y]
  show (RCase x xs) = foo [ "Case", show x, show xs]
  show (RParseError str) = foo [ "ParseError", "str"]
  show RU = "U"
  show (RSrcPos pos tm) = show tm


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
    asDoc p (RVar str) = text str
    asDoc p (RLam str icit x) = par p 0 $ text "\\" ++ wrap icit (text str) <+> text "=>" <+> asDoc 0 x
    -- This needs precedence and operators...
    asDoc p (RApp x y Explicit) = par p 2 $ asDoc 2 x <+> asDoc 3 y
    asDoc p (RApp x y Implicit) = par p 2 $ asDoc 2 x <+> text "{" ++ asDoc 0 y ++ text "}"
    asDoc p RU = text "U"
    asDoc p (RPi Nothing Explicit ty scope) = par p 1 $ asDoc p ty <+> text "->" <+/> asDoc p scope
    asDoc p (RPi (Just x) Explicit ty scope) =
      par p 1 $ text "(" <+> text x <+> text ":" <+> asDoc p ty <+> text ")" <+> text "->" <+/> asDoc p scope
    asDoc p (RPi nm Implicit ty scope) =
      par p 1 $ text "{" <+> text (fromMaybe "_" nm) <+> text ":" <+> asDoc p ty <+> text "}" <+> text "->" <+/> asDoc 1 scope
    asDoc p (RLet x v ty scope) =
      par p 0 $ text "let" <+> text x <+> text ":" <+> asDoc p ty
          <+> text "=" <+> asDoc p v
          <+/> text "in" <+> asDoc p scope
    asDoc p (RSrcPos x y) = asDoc p y
    -- does this exist?
    asDoc p (RAnn x y) = text "TODO - RAnn"
    asDoc p (RLit (LString str)) = text $ interpolate str
    asDoc p (RLit (LInt i)) = text $ show i
    asDoc p (RLit (LBool x)) = text $ show x
    asDoc p (RCase x xs) = text "TODO - RCase"
    asDoc p RImplicit = text "_"
    asDoc p RHole = text "?"
    asDoc p (RParseError str) = text "ParseError \{str}"

export
Pretty Module where
  pretty (MkModule name decls) =
    text "module" <+> text name </> stack (map doDecl decls)
      where
        doDecl : Decl -> Doc
        doDecl (TypeSig nm ty) = text nm <+> text ":" <+> nest 2 (pretty ty)
        doDecl (Def nm tm) = text nm <+> text "=" <+> nest 2 (pretty tm)
        doDecl (DImport nm) = text "import" <+> text nm ++ line
        -- the behavior of nest is kinda weird, I have to do the nest before/around the </>.
        doDecl (Data nm x xs) = text "data" <+> text nm <+> text ":" <+>  pretty x <+> (nest 2 $ text "where" </> stack (map doDecl xs))
        doDecl (DCheck x y) = text "#check" <+> pretty x <+> ":" <+> pretty y

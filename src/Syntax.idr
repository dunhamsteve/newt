module Syntax

import Data.String

Name = String

data Term : Type where

TyTerm = Term

public export
data Literal = LString String | LInt Int | LBool Bool
public export
data RigCount = Rig0 | RigW
public export
data Plicity = Implicit | Explicit | Eq

public export
data Pattern
  = PatVar Name
  | PatCon Name (List (Pattern, RigCount))
  | PatWild
  | PatLit Literal

-- %runElab deriveShow `{Pattern}

-- could be a pair, but I suspect stuff will be added?
public export
data CaseAlt = MkAlt Pattern Term

public export
data Term
  = Var Name
  | Ann Term TyTerm
  | Lit Literal
  | Let (List (Name, Term)) Term
  | Pi Name Plicity Term Term
  | App Term Term
  | Lam Pattern Term
  | Case Term (List CaseAlt)
  | Wildcard
  | ParseError String

-- derive some stuff - I'd like json, eq, show, ...

data Decl : Type where

Telescope: Type
Telescope = List Decl -- pi-forall, always typeSig? 

data ConstrDef = MkCDef Name Telescope

public export
data Decl
  = TypeSig Name TyTerm
  | Def Name Term
  | DImport Name
  | Data Name Telescope (List ConstrDef)

public export
record Module where
  constructor MkModule
  name : Name
  imports : List Name
  decls : List Decl

foo : List String -> String
foo ts = "(" ++ unwords ts ++ ")"


Show Literal where
  show (LString str) = foo [ "LString", show str]
  show (LInt i) = foo [ "LInt", show i]
  show (LBool x) = foo [ "LBool", show x]


export
covering
implementation Show Term

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


export covering
Show Module where
  show (MkModule name imports decls) = foo ["MkModule", show name, show imports, show decls]

Show RigCount where
  show Rig0 = "Rig0"
  show RigW = "RigW"

Show Pattern where
  show (PatVar str) = foo ["PatVar", show str]
  show (PatCon str xs) = foo ["PatCon", show str, assert_total $ show xs]
  show PatWild = "PatWild"
  show (PatLit x) = foo ["PatLit" , show x]

Show CaseAlt where
  show (MkAlt x y)= foo ["MkAlt", show x, assert_total $ show y]

Show Plicity where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show Eq = "Eq"

covering
Show Term where
  show Wildcard = "Wildcard"
  show (Var name) = foo ["Var", show name]
  show (Ann t ty) = foo [ "Ann", show t, show ty]
  show (Lit x) = foo [ "Lit", show x]
  show (Let alts y) = foo [ "Let", show alts, show y]
  show (Pi str x y z) = foo [ "Pi", show str, show x, show y, show z]
  show (App x y) = foo [ "App", show x, show y]
  show (Lam x y) = foo [ "Lam", show x, show y]
  show (Case x xs) = foo [ "Case", show x, show xs]
  show (ParseError str) = foo [ "ParseError", "str"]


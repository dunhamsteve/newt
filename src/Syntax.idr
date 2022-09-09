module Syntax

-- Good enough start, lets parse
-- This is informed by pi-forall and others and is somewhat low level

Name = String

data Term : Type where

TyTerm = Term

data Literal = LString String | LInt Int | LBool Bool
data RigCount = Rig0 | RigW
data Plicity = Implicit | Explicit | Eq

public export
data Pattern
  = PatVar Name
  | PatCon Name (List (Pattern, RigCount))
  | PatWild
  | PatLit Literal

-- could be a pair, but I suspect stuff will be added?
public export
data CaseAlt = MkAlt Pattern Term

public export
data Term
  = Var Name
  | Ann Term TyTerm
  | Lit Literal
  | Let Name Term Term
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

data Decl
  = TypeSig Name RigCount TyTerm
  | Def Name Term
  | Data Name Telescope (List ConstrDef)

record Module where
  constructor MkModule
  name : Name
  imports : List Name
  decls : List Decl

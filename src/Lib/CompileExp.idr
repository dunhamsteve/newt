||| First pass of compilation
||| - work out arities and fully apply functions / constructors (currying)
|||     currying is problemmatic because we need to insert lambdas (η-expand) and
|||     it breaks all of the de Bruijn indices
||| - expand metas (this is happening earlier)
||| - erase stuff (there is another copy that essentially does the same thing)
||| I could make names unique (e.q. on lambdas), but I might want that to vary per backend?
module Lib.CompileExp

import Data.List

import Lib.Types -- Name / Tm
import Lib.TopContext
import Lib.Prettier
import Lib.Util

public export
data CExp : Type

public export
data CAlt : Type where
  CConAlt : String -> List String -> CExp -> CAlt
  -- REVIEW keep var name?
  CDefAlt : CExp -> CAlt
  -- literal
  CLitAlt : Literal -> CExp -> CAlt

data CExp : Type where
  CBnd : Nat -> CExp
  CLam : Name -> CExp -> CExp
  CFun : List Name -> CExp -> CExp
  -- REVIEW This feels like a hack, but if we put CLam here, the
  -- deBruijn gets messed up in code gen
  CApp : CExp -> List CExp -> Nat -> CExp
  -- TODO make DCon/TCon app separate so we can specialize
  -- U / Pi are compiled to type constructors
  CCase : CExp -> List CAlt -> CExp
  CRef : Name -> CExp
  CMeta : Nat -> CExp
  CLit : Literal -> CExp
  CLet : Name -> CExp -> CExp -> CExp
  CLetRec : Name -> CExp -> CExp -> CExp
  CErased : CExp

||| I'm counting Lam in the term for arity.  This matches what I need in
||| code gen.
export
lamArity : Tm -> Nat
lamArity (Lam _ _ _ _ t) = S (lamArity t)
lamArity _ = Z

export
piArity : Tm -> Nat
piArity (Pi _ _ _ quant _ b) = S (piArity b)
piArity _ = Z

||| This is how much we want to curry at top level
||| leading lambda Arity is used for function defs and metas
||| TODO - figure out how this will work with erasure
arityForName : FC -> QName -> M Nat
arityForName fc nm = case lookup nm !get of
  -- let the magic hole through for now (will generate bad JS)
  Nothing => error fc "Name \{show nm} not in scope"
  (Just (MkEntry _ name type Axiom)) => pure 0
  (Just (MkEntry _ name type (TCon strs))) => pure $ piArity type
  (Just (MkEntry _ name type (DCon k str))) => pure k
  (Just (MkEntry _ name type (Fn t))) => pure $ lamArity t
  (Just (MkEntry _ name type (PrimTCon))) => pure $ piArity type
  -- Assuming a primitive can't return a function
  (Just (MkEntry _ name type (PrimFn t uses))) => pure $ piArity type

export
compileTerm : Tm -> M CExp

-- need to eta out extra args, fill in the rest of the apps
apply : CExp -> List CExp -> SnocList CExp -> Nat -> Tm -> M CExp
-- out of args, make one up (fix that last arg)
apply t [] acc (S k) ty = pure $ CApp t (acc <>> []) (S k)
  -- inserting Clam, index wrong?
  -- CLam "eta\{show k}" !(apply t [] (acc :< CBnd k) k ty)
apply t (x :: xs) acc (S k) (Pi y str icit Zero a b) =  apply t xs (acc :< CErased) k b
apply t (x :: xs) acc (S k) (Pi y str icit Many a b) =  apply t xs (acc :< x) k b
-- see if there is anything we have to handle here
apply t (x :: xs) acc (S k) ty = error (getFC ty) "Expected pi \{showTm ty}. Overapplied function that escaped type checking?"
-- once we hit zero, we fold the rest
apply t ts acc 0 ty = go (CApp t (acc <>> []) Z) ts
  where
    go : CExp -> List CExp -> M CExp
    -- drop zero arg call
    go (CApp t [] Z) args = go t args
    go t [] = pure t
    go t (arg :: args) = go (CApp t [arg] 0) args

-- apply : CExp -> List CExp -> SnocList CExp -> Nat -> M CExp
-- -- out of args, make one up
-- apply t [] acc (S k) = pure $
--   CLam "eta\{show k}" !(apply t [] (acc :< CBnd k) k)
-- apply t (x :: xs) acc (S k) = apply t xs (acc :< x) k
-- apply t ts acc 0 = go (CApp t (acc <>> [])) ts
--   where
--     go : CExp -> List CExp -> M CExp
--     -- drop zero arg call
--     go (CApp t []) args = go t args
--     go t [] = pure t
--     go t (arg :: args) = go (CApp t [arg]) args

compileTerm (Bnd _ k) = pure $ CBnd k
-- need to eta expand to arity
compileTerm t@(Ref fc nm _) = do
  top <- get
  let Just (MkEntry _ _ type _) = lookup nm top
          | Nothing => error fc "Undefined name \{nm}"
  apply (CRef (show nm)) [] [<] !(arityForName fc nm) type

compileTerm (Meta _ k) = pure $ CRef "meta$\{show k}" -- FIXME
compileTerm (Lam _ nm _ _ t) = pure $ CLam nm !(compileTerm t)
compileTerm tm@(App _ _ _) with (funArgs tm)
  _ | (Meta _ k, args) = do
        info (getFC tm) "Compiling an unsolved meta \{showTm tm}"
        pure $ CApp (CRef "Meta\{show k}") [] Z
  _ | (t@(Ref fc nm _), args) = do
        args' <- traverse compileTerm args
        arity <- arityForName fc nm
        top <- get
        let Just (MkEntry _ _ type _) = lookup nm top
          | Nothing => error fc "Undefined name \{nm}"
        apply (CRef (show nm)) args' [<] arity type
  _ | (t, args) = do
        debug "apply other \{pprint [] t}"
        t' <- compileTerm t
        args' <- traverse compileTerm args
        apply t' args' [<] 0 (UU emptyFC)
        -- error (getFC t) "Don't know how to apply \{showTm t}"
compileTerm (UU _) = pure $ CRef "U"
compileTerm (Pi _ nm icit rig t u) = pure $ CApp (CRef "PiType") [ !(compileTerm t), CLam nm !(compileTerm u)] Z
compileTerm (Case _ t alts) = do
  t' <- compileTerm t
  alts' <- traverse (\case
    CaseDefault tm => pure $ CDefAlt !(compileTerm tm)
    -- we use the base name for the tag, some primitives assume this
    CaseCons (QN ns nm) args tm => pure $ CConAlt nm args !(compileTerm tm)
    CaseLit lit tm => pure $ CLitAlt lit !(compileTerm tm)) alts
  pure $ CCase t' alts'
compileTerm (Lit _ lit) = pure $ CLit lit
compileTerm (Let _ nm t u) = pure $ CLet nm !(compileTerm t) !(compileTerm u)
compileTerm (LetRec _ nm _ t u) = pure $ CLetRec nm !(compileTerm t) !(compileTerm u)
compileTerm (Erased _) = pure CErased

export
compileFun : Tm -> M CExp
compileFun tm = go tm [<]
  where
    go : Tm -> SnocList String -> M CExp
    go (Lam _ nm _ _ t) acc = go t (acc :< nm)
    go tm [<] = compileTerm tm
    go tm args = pure $ CFun (args <>> []) !(compileTerm tm)



||| First pass of compilation
||| - work out arities and fully apply functions / constructors
||| - expand metas
||| I could make names unique (e.q. on lambdas), but I might want that to vary per backend?
module Lib.CompileExp

import Data.List

import Lib.Types -- Name / Tm
import Lib.TopContext
import Lib.TT -- lookupMeta
import Lib.Util

public export
data CExp : Type

public export
data CAlt : Type where
  CConAlt : String -> List String -> CExp -> CAlt
  -- REVIEW keep var name?
  CDefAlt : CExp -> CAlt
  -- literal

data CExp : Type where
  CBnd : Nat -> CExp
  CLam : Name -> CExp -> CExp
  CFun : List Name -> CExp -> CExp
  CApp : CExp -> List CExp -> CExp
  -- TODO make DCon/TCon app separate so we can specialize
  -- U / Pi are compiled to type constructors
  CCase : CExp -> List CAlt -> CExp
  CRef : Name -> CExp
  CMeta : Nat -> CExp
  CLit : Literal -> CExp
  CLet : Name -> CExp -> CExp -> CExp

||| I'm counting Lam in the term for arity.  This matches what I need in
||| code gen.
export
getArity : Tm -> Nat
getArity (Lam _ _ t) = S (getArity t)
getArity _ = Z

export
piArity : Tm -> Nat
piArity (Pi _ _ _ _ b) = S (piArity b)
piArity _ = Z

arityForName : FC -> Name -> M Nat
arityForName fc nm = case lookup nm !get of
  Nothing => error fc "Name \{show nm} not in scope"
  (Just (MkEntry name type Axiom)) => pure 0
  (Just (MkEntry name type (TCon strs))) => pure 0 -- FIXME
  (Just (MkEntry name type (DCon k str))) => pure k
  (Just (MkEntry name type (Fn t))) => pure $ getArity t
  (Just (MkEntry name type (PrimTCon))) => pure 0
  -- Assuming a primitive can't return a function
  (Just (MkEntry name type (PrimFn t))) => pure $ piArity type

export
compileTerm : Tm -> M CExp

-- need to eta out extra args, fill in the rest of the apps
apply : CExp -> List CExp -> SnocList CExp -> Nat -> M CExp
-- out of args, make one up
apply t [] acc (S k) = pure $
  CLam "eta\{show k}" !(apply t [] (acc :< CBnd k) k)
apply t (x :: xs) acc (S k) = apply t xs (acc :< x) k
apply t ts acc 0 = go (CApp t (acc <>> [])) ts
  where
    go : CExp -> List CExp -> M CExp
    go t [] = pure t
    go t (arg :: args) = go (CApp t [arg]) args

compileTerm (Bnd _ k) = pure $ CBnd k
-- need to eta expand to arity
compileTerm t@(Ref fc nm _) = apply (CRef nm) [] [<] !(arityForName fc nm)

-- need to zonk
compileTerm (Meta _ k) = pure $ CRef "meta$\{show k}" -- FIXME
compileTerm (Lam _ nm t) = pure $ CLam nm !(compileTerm t)
compileTerm tm@(App _ _ _) with (funArgs tm)
  _ | (Meta _ k, args) = do
        -- FIXME get arity or zonk?
        -- Maybe we should be storing the Term without the lambdas...
        -- we don't have a lot here, but JS has an "environment" with names and
        -- we can assume fully applied.
        meta <- lookupMeta k
        args' <- traverse compileTerm args
        -- apply (CRef "Meta\{show k}") args' [<] 0
        arity <- case meta of
                -- maybe throw
                (Unsolved x j xs) => pure 0
                (Solved j tm) => pure $ getArity !(quote 0 tm)
        apply (CRef "Meta\{show k}") args' [<] arity
  _ | (t@(Ref fc nm _), args) = do
        args' <- traverse compileTerm args
        arity <- arityForName fc nm
        apply (CRef nm) args' [<] arity
  _ | (t, args) = do
        debug "apply other \{pprint [] t}"
        t' <- compileTerm t
        args' <- traverse compileTerm args
        apply t' args' [<] 0
compileTerm (U _) = pure $ CRef "U"
compileTerm (Pi _ nm icit t u) = pure $ CApp (CRef "PiType") [ !(compileTerm t), CLam nm !(compileTerm u)]
compileTerm (Case _ t alts) = do
  t' <- compileTerm t
  alts' <- traverse (\case
    CaseDefault tm => pure $ CDefAlt !(compileTerm tm)
    CaseCons nm args tm => pure $ CConAlt nm args !(compileTerm tm)) alts
  pure $ CCase t' alts'
compileTerm (Lit _ lit) = pure $ CLit lit
compileTerm (Let _ nm t u) = pure $ CLet nm !(compileTerm t) !(compileTerm u)

export
compileFun : Tm -> M CExp
compileFun tm = go tm []
  where
    go : Tm -> List String -> M CExp
    go (Lam _ nm t) acc = go t (nm :: acc)
    go tm args = pure $ CFun (reverse args) !(compileTerm tm)




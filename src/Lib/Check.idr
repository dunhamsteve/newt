module Lib.Check

import Control.Monad.Error.Interface
import Control.Monad.Identity
import Lib.Parser.Impl
import Data.Vect
import Data.String
import Lib.TT
import Syntax

record Context (n : Nat) (f : Nat)  where
  -- review this
  env : Env f n -- Vect n (Val f)
  types : List (String, Val f)
  pos : SourcePos


extend : Context n f -> Val f -> Context (S n) f
extend ctx ty = { env := ty :: ctx.env } ctx

-- cribbed this, it avoids MonadError String m => everywhere
parameters {0 m : Type -> Type} {auto _ : MonadError String m}

  infer : {f : Nat} -> Context n f -> Raw -> m (Tm n, Val f)
  -- I think I'm hand-waving n here, probably need it in Context
  check : {f : Nat} -> Context n f -> Raw -> Val f -> m (Tm n)

  check ctx (RLam _ _ _) ty = ?ch_rhs
  check ctx tm ty = do
    (tm', ty') <- infer ctx tm
    if quote _ ty /= quote _ ty' then
        throwError "type mismatch"
      else pure tm'


  infer ctx (RVar nm) = go 0 ctx.types
    where
      go : Nat -> List (String, Val f) -> m (Tm n, Val f)
      go i [] = throwError "\{show nm} not in scope"
      -- REVIEW Local or Bnd (ezoo does not have both)
      go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd ?i_not_fin, ty) 
        else go (i + 1) xs

      
    -- need environment of name -> type..
  infer ctx (RApp t u icit) = do 
    -- icit will be used for insertion, lets get this working first...
    (t, tty) <- infer ctx t
    case tty of
      (VPi str icit' a b) => do
        u <- check ctx u a
        
        -- is zero right here?
        -- I have ctx.env here and TypeTheory has []
        -- maybe because I'm not substing?
        pure (App t u, b 0 (eval ctx.env t))
      _ => throwError "Expected Pi type"
      
    -- FIXME ctx.env?
    -- vtya <- nf ctx.env tma
    
  infer ctx RU = pure (U, VU) -- YOLO
  infer ctx (RPi nm icit ty ty2) = do
    ty' <- check ctx ty VU
    let vty' := eval ctx.env ty'
    -- gallais and the source paper have subst here.  They're using Tm rather
    -- than raw. Lets look at the zoo.
    -- maybe run through zoo2 well typed...
    -- it just binds vty' into the environment and evaluates 
    -- Kovacs is sticking the type vty' and the value Var l into the context
    -- and letting the Ix pick up the Var l from the context
    -- gallais/paper are subst the Var l into the Tm.
    -- yaffle just pushes to the environment, but it's a list of binders
    -- so types, names, no values
    ty2' <- check (extend ctx vty') ty2 VU
    let nm := fromMaybe "_" nm
    pure (Pi nm icit ty' ty2', VU)
  infer ctx (RLet str tm tm1 tm2) = ?rhs_5
  infer ctx (RSrcPos x tm) = infer ({pos := x} ctx) tm
  infer ctx (RAnn tm rty) = do
    ty <- check ctx rty VU
    let vty = eval ctx.env ty 
    tm <- check ctx tm vty
    pure (tm, vty)

  infer ctx (RLam str icit tm) = throwError "can't infer lambda"

  infer ctx _ = ?later
  -- I don't have types for these yet...
  -- infer ctx (RLit (LString str)) = ?rhs_10
  -- infer ctx (RLit (LInt i)) = ?rhs_11
  -- infer ctx (RLit (LBool x)) = ?rhs_12
  -- infer ctx RHole = ?todo_meta2
  -- infer ctx (RParseError str) = ?todo_insert_meta
  -- infer ctx (RCase tm xs) = ?rhs_9

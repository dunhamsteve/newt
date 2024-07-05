module Lib.Check

import Control.Monad.Error.Interface
import Control.Monad.Identity
import Lib.Parser.Impl
import Data.Vect
import Data.String
import Lib.TT
import Lib.TopContext
import Syntax

-- cribbed this, it avoids MonadError String m => everywhere
parameters {0 m : Type -> Type} {auto _ : MonadError Error m} (top : TopContext)
  export
  infer : Context -> Raw -> m (Tm, Val)

  export
  check : Context -> Raw -> Val -> m Tm
  check ctx (RSrcPos x tm) ty = check ({pos := x} ctx) tm ty
  check ctx (RLam nm icit tm) ty = case ty of                    
                    (VPi pinm icit a b) => do
                      -- TODO icit
                      let var = VVar (length ctx.env)
                      let ctx' = extend ctx nm a
                      tm' <- check ctx' tm (b $$ var)
                      pure $ Lam nm icit tm'
                    
                    -- So it gets stuck for `List a`, not a pi type, and we want the
                    -- (This is not a data constructor, but a church encoding)
                    -- List reduces now and we're stuck for `Nat`.

                    other => error [(DS "Expected pi type, got \{show $ quote 0 ty}")]
  check ctx tm ty = do
    (tm', ty') <- infer ctx tm
    if quote 0 ty /= quote 0 ty' then
        error [DS "type mismatch"]
      else pure tm'

  infer ctx (RVar nm) = go 0 ctx.types
    where
      go : Nat -> Vect n (String, Val) -> m (Tm, Val)
      go i [] = case lookup nm top of
        Just (MkEntry name ty (Fn t)) => pure (Ref nm (Just t), eval [] CBN ty)
        Just (MkEntry name ty _) => pure (Ref nm Nothing, eval [] CBN ty)
        Nothing => error [DS "\{show nm} not in scope"]
      go i ((x, ty) :: xs) = if x == nm then pure $ (Bnd i, ty) 
        else go (i + 1) xs
    -- need environment of name -> type..
  infer ctx (RApp t u icit) = do 
    -- icit will be used for insertion, lets get this working first...
    (t, tty) <- infer ctx t
    case tty of
      (VPi str icit' a b) => do
        u <- check ctx u a
        pure (App t u, b $$ eval ctx.env CBN t)
      _ => error [DS "Expected Pi type"]
  infer ctx RU = pure (U, VU) -- YOLO
  infer ctx (RPi nm icit ty ty2) = do
    ty' <- check ctx ty VU
    let vty' := eval ctx.env CBN ty'
    let nm := fromMaybe "_" nm
    ty2' <- check (extend ctx nm vty') ty2 VU
    pure (Pi nm icit ty' ty2', VU)
  infer ctx (RLet str tm tm1 tm2) = ?rhs_5
  infer ctx (RSrcPos x tm) = infer ({pos := x} ctx) tm
  infer ctx (RAnn tm rty) = do
    ty <- check ctx rty VU
    let vty = eval ctx.env CBN ty 
    tm <- check ctx tm vty
    pure (tm, vty)

  infer ctx (RLam str icit tm) = error [DS "can't infer lambda"]

  infer ctx _ = error [DS "TODO"]

  -- I don't have types for these yet...
  -- infer ctx (RLit (LString str)) = ?rhs_10
  -- infer ctx (RLit (LInt i)) = ?rhs_11
  -- infer ctx (RLit (LBool x)) = ?rhs_12
  -- infer ctx (RCase tm xs) = ?rhs_9
  -- infer ctx RHole = ?todo_meta2
  -- The idea here is to insert a hole for a parse error
  -- infer ctx (RParseError str) = ?todo_insert_meta

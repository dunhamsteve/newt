-- I'm not sure this is related, or just a note to self (Presheaves on Porpoise)

-- maybe watch https://www.youtube.com/watch?v=3gef0_NFz8Q
-- or drop the indices for now.

-- ***
-- Kovacs has icity on App, and passes it around, but I'm not sure where it is needed since the insertion happens based on Raw.

module Lib.TT
-- For SourcePos
import Lib.Parser.Impl
import Lib.Prettier
import Lib.Types
import Control.Monad.Error.Interface

import Data.IORef
import Data.Fin
import Data.List
import Data.Vect
import Data.SortedMap

-- Errors cribbed from pi-forall
public export
data ErrorSeg : Type where
  DD : Pretty a => a -> ErrorSeg
  DS : String -> ErrorSeg

toDoc : ErrorSeg -> Doc
toDoc (DD x) = pretty x
toDoc (DS str) = text str

export
error : {auto ctx : Context} -> List ErrorSeg -> M a
error xs = throwError $ E ctx.pos (render 80 $ spread $ map toDoc xs)

export
error' : String -> M a
error' msg = throwError $ E (0,0) msg

-- order does indeed matter on the meta arguments
-- because of dependent types (if we want something well-typed back out)

export
freshMeta : Context -> M Tm
freshMeta ctx = do
  mc <- readIORef ctx.metas
  putStrLn "INFO at \{show ctx.pos}: fresh meta \{show mc.next}"
  writeIORef ctx.metas $ { next $= S, metas $= (Unsolved ctx.pos mc.next ctx.bds ::) } mc
  pure $ applyBDs 0 (Meta mc.next) ctx.bds
  where
  -- hope I got the right order here :)
  applyBDs : Nat -> Tm -> List BD -> Tm
  applyBDs k t [] = t
  -- review the order here
  applyBDs k t (Bound :: xs) = App (applyBDs (S k) t xs) (Bnd k)
  applyBDs k t (Defined :: xs) = applyBDs (S k) t xs

export
lookupMeta : Nat -> M MetaEntry
lookupMeta ix = do
  ctx <- get
  mc <- readIORef ctx.metas
  go mc.metas
  where
    go : List MetaEntry -> M MetaEntry
    go [] = error' "Meta \{show ix} not found"
    go (meta@(Unsolved _ k ys) :: xs) = if k == ix then pure meta else go xs
    go (meta@(Solved k x) :: xs) = if k == ix then pure meta else go xs

export
solveMeta : TopContext -> Nat -> Val -> M ()
solveMeta ctx ix tm = do
  mc <- readIORef ctx.metas
  metas <- go mc.metas [<]
  writeIORef ctx.metas $ {metas := metas} mc
  where
    go : List MetaEntry -> SnocList MetaEntry -> M (List MetaEntry)
    go [] _ = error' "Meta \{show ix} not found"
    go (meta@(Unsolved pos k _) :: xs) lhs = if k == ix
      then do
        putStrLn "INFO at \{show pos}: solve \{show k} as \{show tm}"
        pure $ lhs <>> (Solved k tm :: xs)
      else go xs (lhs :< meta)
    go (meta@(Solved k _) :: xs) lhs = if k == ix
      then error' "Meta \{show ix} already solved!"
      else go xs (lhs :< meta)

export partial
Show Context where
  show ctx = "Context \{show $ map fst $ ctx.types}"

-- TODO Pretty Context


||| add a binding to environment
export
extend : Context -> String -> Val -> Context
extend ctx name ty =
    { lvl $= S, env $= (VVar ctx.lvl [<] ::), types $= ((name, ty) ::), bds $= (Bound ::) } ctx

-- I guess we define things as values?
export
define : Context -> String -> Val -> Val -> Context
define ctx name val ty =
  { lvl $= S, env $= (val ::), types $= ((name,ty) ::), bds $= (Defined ::) } ctx


-- not used
lookup : Context -> String -> M Val
lookup ctx nm = go ctx.types
  where
    go : Vect n (String,Val) -> M Val
    go [] = error' "Name \{nm} not in scope"
    go ((n, ty) :: xs) = if n == nm then pure ty else go xs


-- Need to wire in the metas...
-- if it's top / ctx / IORef, I also need IO...
-- if I want errors, I need m anyway.  I've already got an error down there.



export
eval : Env -> Mode -> Tm -> M Val

public export
($$) : {auto mode : Mode} -> Closure -> Val -> M Val
($$) {mode} (MkClosure env tm) u = eval (u :: env) mode tm

public export
infixl 8 $$

export
vapp : Val -> Val -> M Val
vapp (VLam _ t) u = t $$ u
vapp (VVar k sp) u = pure $ VVar k (sp :< u)
vapp (VRef nm sp) u = pure $ VRef nm (sp :< u)
vapp (VMeta k sp) u = pure $ VMeta k (sp :< u)
vapp t u = error' "impossible in vapp \{show t} to \{show u}"

export
vappSpine : Val -> SnocList Val -> M Val
vappSpine t [<] = pure t
vappSpine t (xs :< x) = vapp !(vappSpine t xs) x

bind : Val -> Env -> Env
bind v env = v :: env

-- Do we want a def in here instead?  We'll need DCon/TCon eventually
-- I need to be aggressive about reduction, I guess. I'll figure it out
-- later, maybe need lazy glued values.
eval env mode (Ref x (Just tm)) = eval env mode tm
eval env mode (Ref x Nothing) = pure $ VRef x [<]
eval env mode (App t u) = vapp !(eval env mode t) !(eval env mode u)
eval env mode U = pure VU
eval env mode (Meta i) =
  case !(lookupMeta i) of
        (Unsolved _ k xs) => pure $ VMeta i [<]
        (Solved k t) => pure $ t
eval env mode (Lam x t) = pure $ VLam x (MkClosure env t)
eval env mode (Pi x icit a b) = pure $ VPi x icit !(eval env mode a) (MkClosure env b)
eval env mode (Let x ty t u) = eval (!(eval env mode t) :: env) mode u
eval env mode (Bnd i) = case getAt i env of
  Just rval => pure rval
  Nothing => error' "Bad deBruin index \{show i}"

export
quote : (lvl : Nat) -> Val -> M Tm

quoteSp : (lvl : Nat) -> Tm -> SnocList Val -> M Tm
quoteSp lvl t [<] = pure t
quoteSp lvl t (xs :< x) =
  pure $ App !(quoteSp lvl t xs) !(quote lvl x)
  -- quoteSp lvl (App t !(quote lvl x)) xs  -- snoc says previous is right

quote l (VVar k sp) = if k < l
  then quoteSp l (Bnd ((l `minus` k) `minus` 1)) sp -- level to index
  else ?borken
quote l (VMeta i sp) = quoteSp l (Meta i) sp
quote l (VLam x t) = pure $ Lam x !(quote (S l) !(t $$ VVar l [<]))
quote l (VPi x icit a b) = pure $ Pi x icit !(quote l a) !(quote (S l) !(b $$ VVar l [<]))
quote l VU = pure U
quote l (VRef n sp) = quoteSp l (Ref n Nothing) sp

-- Can we assume closed terms?
-- ezoo only seems to use it at [], but essentially does this:
export
nf : Env -> Tm -> M Tm
nf env t = quote (length env) !(eval env CBN t)



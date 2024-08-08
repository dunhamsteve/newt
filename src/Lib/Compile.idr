module Lib.Compile

import Lib.Types
import Lib.Prettier

-- turn Tm into javscript


-- JS AST (or just write a Doc?)

data JSExp : Type where

data JSStmt : Type where

-- Need to sort out



compile : Nat -> Tm -> Doc
-- Oh, we don't have local names...
compile l (Bnd _ k) = text "_\{show k}"
-- this is tied to Bnd
-- And we probably want `{...}` with statements...
compile l (Lam _ str t) = text "(_\{show l}) => " <+> compile (S l) t
compile l (Ref _ str mt) = text str
compile l (App _ t u) = compile l t <+> "(" <+> compile l u <+> ")"

compile l (U _) = "undefined"
compile l (Pi _ str icit t u) = "undefined"
compile l (Meta _ k) = text "ZONKME \{show k}"
compile l (Case fc tm alts) = ?rhs_8

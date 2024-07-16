module Lib.Compile

import Lib.Types
import Lib.Prettier

-- turn Tm into javscript


-- JS AST (or just write a Doc?)

data JSExp : Type where

data JSStmt : Type where

compile : Nat -> Tm -> Doc
-- Oh, we don't have local names...
compile l (Bnd k) = text "_\{show k}"
-- this is tied to Bnd
-- And we probably want `{...}` with statements...
compile l (Lam str t) = text "(_\{show l}) => " <+> compile (S l) t
compile l (Ref str mt) = text str
compile l (App t u) = compile l t <+> "(" <+> compile l u <+> ")"

compile l U = "undefined"
compile l (Pi str icit t u) = "undefined"
compile l (Meta k) = text "ZONKME \{show k}"

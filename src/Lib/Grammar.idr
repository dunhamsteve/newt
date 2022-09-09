module Lib.Grammar

-- Derived from Parser/Core.idr - revisit later when we want to be stack safe
-- For simplicity (for now), it drops consumed flag from the type, which I think was
-- there for totality checking.  May want it back someday.

data Grammar : (state : Type) -> (tok : Type) -> Type -> Type where
  EOF : Grammar state tok ()
  Empty : a -> Grammar state tok a
  Fail : String -> Grammar state tok a
  Commit : Grammar state tok ()
  Alt : Grammar state tok ty -> Lazy (Grammar state tok ty) -> Grammar state tok ty
  Seq : Grammar state tok a -> (a -> Grammar state tok b) -> Grammar state tok b

Functor (Grammar state tok) where
  map f (Fail str) = Fail str
  map f (Alt x y) = Alt (map f x) (map f y)
  map f (Seq x g) = ?todo_4
  map f (Empty v) = Empty (f v)
  -- Empty / EOF
  map f p = Seq p (Empty . f)
  
Applicative (Grammar state tok) where
  pure a = Empty a
  x <*> y = ?hole3

Alternative (Grammar state tok) where 
  empty = ?hole2
  (<|>) = Alt

Monad (Grammar state tok) where
  (>>=) = Seq

ParseError : Type

data ParseResult : Type -> Type -> Type -> Type where
  Failure : (commit : Bool) -> List ParseError -> ParseResult state tok ty

doParse : Semigroup state =>
          state ->
          (commit : Bool) ->
          Grammar state tok ty ->
          List tok ->
          ParseResult state tok ty
doParse = ?todo

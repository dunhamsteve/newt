Newt is a self-hosted, dependent typed programming language that compiles to javascript and borrows a lot of syntax from Idris and Agda. This document is a quick tour of the language as a literate newt document. Code blocks fenced with `newt` are processed by the compiler and language server.

## Comments

Comments follow Lean, because I find their block comment format easier to type on a US keyboard:
```newt
/-
Block comments look like this.
-/

-- One line comments begin with two hyphens
```


Every file begins with a `module` declaration which must match the filename.

```newt
module Tour
```

We can import other modules at the top of the file. Cycles are an error, but diamonds are ok. The prelude is not imported by default. Only explicitly imported modules are in scope. Local names override imported names.

```
import Prelude
```

The universe is called `U` and are doing type in type. We have quantity 0 and ω.

## Inductive Types

Inductive type definitions are similar to Idris, Agda, or Haskell. We have a long form format for indexed types:

```newt
data Nat : U where
  Z : Nat
  S : Nat -> Nat
```

There also is an abbreviated syntactic sugar for simple types:
```newt
data Tree a = Node a (Tree a) (Tree a) | Leaf
```


Multiple names are allowed on the left:
```newt
data Bool : U where
  True False : Bool
```

As in Idris, anything Nat-shaped after erasure is turned into numbers at runtime. And Enum shaped data becomes a number at runtime.

```newt
data Answer = Yes | No | Maybe
```

## FUNCTIONS AND PATTERN MATCHING

Function definitions are equations using dependent pattern matching

```newt
plus : Nat -> Nat -> Nat
plus Z m = m
plus (S n) m = S (plus n m)
```

We can also have case statements on the right side
the core language includes case statements
here `\` is used for a lambda expression:

```newt
plus' : Nat -> Nat -> Nat
plus' = \ n m => case n of
    Z => m
    S n => S (plus' n m)
```

"impossible" clauses work like Agda - a `()` is placed where
no constructor is valid, and the right hand side is omitted:

```newt
data Void : U where

absurd : ∀ a. Void → a
absurd ()
```

We can define mixfix operators, but we don't allow ambiguity. So you can't have both `[_]` and `[_,_]`. See
the `Reasoning.newt` sample file for a mixfix example.

```newt
infixl 2 _≡_
```

Here is an equality, like Idris, everything goes to the right of the colon
Implicits are denoted with braces `{ }`
Unlike idris, you have to declare all of your implicits
```newt
data _≡_ : {0 A : U} -> A -> A -> U where
  Refl : {0 A : U} {0 a : A} -> a ≡ a
```
And now the compiler can verify that 1 + 1 = 2
```newt            
test : plus (S Z) (S Z) ≡ S (S Z)
test = Refl
```

## HOLES AND LSP SUPPORT

We can leave a hole in an expression with ?
On hover, the editor will show the expected type and the scope
There are also code actions to intro a constructor or variable from scope

On the left, we have code actions to case split the patterns.
If a case were missing, we'd have an option to add missing cases
```newt
foo : Nat -> Nat -> Nat
foo a b = ?
```

The LSP also supports additional operations that are not exposed in the playground:
- go to definition
- show references
- rename in scope
- warnings for unused variables


## PRIMITIVE FUNCTIONS

Newt compiles to javascript, there is a tab to the right that shows the
javascript output.

We can define native types, if the type is left off, it defaults to U

```newt
ptype SomePrimType : U
```

The types Int, String, Char are special. Primitive numbers, strings,
and characters inhabit them, respectively. We can match on these primitives, but
must provide a default case:

```newt
isVowel : Char -> Bool
isVowel 'a' = True
isVowel 'e' = True
isVowel 'i' = True
isVowel 'o' = True
isVowel 'u' = True
isVowel _ = False
```

Primitive functions have a type and a javascript definition:

```newt
pfunc addInt : Int -> Int -> Int := `(x,y) => x + y`
pfunc addString : String -> String -> String := `(x,y) => x + y`
```

For the scheme backend, the primitives are defined in a separate file.

## Type classes

Let's say we want a generic `_+_` operator
```newt
infixl 7 _+_
```
We define a class:
```newt
class Add a where
  _+_ : a -> a -> a
```
This creates a generic function:
```
_+_ : ∀ a. {{Add a}} → a → a → a
```

Here the {{Add a}} is an "auto" implicit, the compiler will find a unique solution
and fill it in as an argument when `+` is invoked.

and an instance for `Nat`
```newt
instance Add Nat where
  Z + m = m
  (S n) + m = S (n + m)
```
And it will be used when we add two `Nat` values

```newt
two : Nat
two = S Z + S Z

instance Add Int where
  _+_ = addInt

infixr 7 _++_
class Concat a where
  _++_ : a → a → a

instance Concat String where
  _++_ = addString
```

Now we define Monad
```newt
class Monad (m : U -> U) where
  pure : ∀ a. a -> m a
  bind : ∀ a b. m a -> (a -> m b) -> m b
```

we can declare multiple infix operators at once
```newt
infixl 1 _>>=_ _>>_

_>>=_ : ∀ m a b. {{Monad m}} -> m a -> (a -> m b) -> m b
_>>=_ ma amb = bind ma amb

_>>_ :  ∀ m a b. {{Monad m}} -> m a -> m b -> m b
ma >> mb = ma >>= (λ _ => mb)
```

Now we define list and show it is a monad.

```newt
infixr 3 _::_
data List : U -> U where
  Nil : ∀ A.  List A
  _::_ : ∀ A. A -> List A -> List A

instance Monad List where
  pure a = a :: Nil
  bind Nil f = Nil
  bind (x :: xs) f = f x ++ bind xs f
```

and has the _++_ operator

```newt
instance ∀ a. Concat (List a) where
  Nil ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)
```

A utility function used in generating Show instances below:

```newt
joinBy : String → List String → String
joinBy _ Nil = ""
joinBy _ (x :: Nil) = x
joinBy s (x :: y :: xs) = joinBy s ((x ++ s ++ y) :: xs)
```

We define a product of two types (→ can be used in lieu of ->)
```newt
infixr 1 _,_ _×_
data _×_ : U → U → U where
  _,_ : ∀ A B. A → B → A × B
```

The `_>>=_` operator is used for desugaring `do` blocks

```newt
prod : ∀ A B. List A → List B → List (A × B)
prod xs ys = do
  x <- xs
  y <- ys
  pure (x, y)
```

## Derive

The prelude defines Eq, Ord, and Show
Instances of these can be derived automatically with `derive`

```newt
infixl 6 _==_
class Eq a where
  _==_ : a → a → Bool

derive Eq Nat

class Show a where
  show : a → String

derive Show Nat
```

If you place the cursor on a derive statement, there is a code action
to expand the derived code in-place

## IO and main

The compilation does dead code elimination, so we define a main function to
trigger code generation.

First we build the IO Monad:

```newt
data Unit = MkUnit

ptype World

data IORes a = MkIORes a World
```

`alias` is sugar for an erased function that returns a type
```newt
alias IO a = World -> IORes a

instance Monad IO where
  bind ma mab = \ w => case ma w of
    MkIORes a w => mab a w
  pure = MkIORes
```

A primitive to print (because we do dead code elimination, we need to declare what globals are used by the primitive):

```newt
pfunc putStrLn uses (MkIORes MkUnit) : String -> IO Unit := `(s) => (w) => {
  console.log(s)
  return Tour_MkIORes(Tour_MkUnit, w)
}`
```

And our main function:
```newt
main : IO Unit
main = do
  putStrLn "Hello, World!"
  putStrLn $ show (S (S Z))
```

-- https://personal.cis.strath.ac.uk/conor.mcbride/fooling/Jigger.agda
module Jigger where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

max : {n : Nat} -> Fin (suc n)
max {zero} = zero
max {suc n} = suc (max {n})

embed : {n : Nat} -> Fin n -> Fin (suc n)
embed zero = zero
embed (suc n) = suc (embed n)

var : (m : Nat){n : Nat} -> Fin (suc (m + n))
var zero = max
var (suc m) = embed (var m)

data Tm (n : Nat) : Set where
  V : Fin n -> Tm n
  _$_ : Tm n -> Tm n -> Tm n
  L : Tm (suc n) -> Tm n

l : {m : Nat} -> (({n : Nat} -> Tm (suc (m + n))) -> Tm (suc m)) ->
    Tm m
l {m} f = L (f \{n} -> V (var m {n}))

myTest : Tm zero
myTest = l \ f -> l \ x -> f $ (f $ x)


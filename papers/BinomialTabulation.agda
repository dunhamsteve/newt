-- Checked with Agda 2.6.4.3 and Standard Library 2.0

{-# OPTIONS --safe --large-indices --no-forced-argument-recursion #-}

module BinomialTabulation where

open import Function renaming (_$_ to infixr 5 _$_)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality

variable
  a b c          : Set
  k m n          : ℕ
  x              : a
  xs             : Vec a n
  p p' q q' r r' : a → Set

--------
-- Section 2.1

module ShapeIndexing where

  data B : ℕ → ℕ → Set → Set where
    tipZ : a             → B n        zero   a
    tipS : a             → B (suc k) (suc k) a
    bin  : B n (suc k) a
         → B n      k  a → B (suc n) (suc k) a

  bounded : B n k a → k ≤ n
  bounded (tipZ _)  = z≤n
  bounded (tipS _)  = ≤-refl
  bounded (bin _ u) = s≤s (bounded u)

  unbounded : B k (suc k) a → ⊥
  unbounded (bin t u) = unbounded u
  unbounded (tipS t) = ?

  mapB : (a → b) → B n k a → B n k b
  mapB f (tipZ x)  = tipZ (f x)
  mapB f (tipS x)  = tipS (f x)
  mapB f (bin t u) = bin (mapB f t) (mapB f u)

  unTipB : B n n a → a
  unTipB (tipZ x)  = x
  unTipB (tipS x)  = x
  unTipB (bin t _) = ⊥-elim (unbounded t)

  zipBWith : (a → b → c) → B n k a → B n k b → B n k c
  zipBWith f (tipZ x)   (tipZ y)   = tipZ (f x y)
  zipBWith f (tipS x)   u          = tipS (f x (unTipB u))
  zipBWith f (bin t _)  (tipS _)   = ⊥-elim (unbounded t)
  zipBWith f (bin t t') (bin u u') = bin (zipBWith f t u) (zipBWith f t' u')

  cd : 1 ≤ k → k < n → B n k a → B n (1 + k) (Vec a (1 + k))
  cd () _            (tipZ _)
  cd _ 1+k<1+k       (tipS _)                       = ⊥-elim (<-irrefl refl 1+k<1+k)
  cd _ _             (bin   (tipS y  )   (tipZ z )) = tipS (y ∷ z ∷ [])
  cd _ _             (bin   (tipS y  ) u@(bin _ _)) = tipS (y ∷ unTipB (cd (s≤s z≤n) ≤-refl u))
  cd _ _             (bin t@(bin t' _)   (tipZ z )) = bin (cd ≤-refl (s≤s (bounded t')) t) (mapB (_∷ (z ∷ [])) t)
  cd _ 2+n<2+n       (bin   (bin _ _ )   (tipS _ )) = ⊥-elim (<-irrefl refl 2+n<2+n)
  cd _ (s≤s 1+k<1+n) (bin t@(bin t' _) u@(bin _ _)) = bin (cd (s≤s z≤n) (s≤s (bounded t')) t) (zipBWith _∷_ t (cd (s≤s z≤n) 1+k<1+n u))
  -- newt doesn't rule this out
  -- cd _ 2+n<2+n       (bin   (tipS y )   (tipS z )) = ?
  
  -- end of module ShapeIndexing

--------
-- Section 2.2

module RestrictedSpecification where

  variable h : Vec a k → b

  data B' : (n k : ℕ) (b : Set) → (Vec a k → b) → Vec a n → Set where
    tipZ : (y : b) → y ≡ h []                    → B' n        zero   b h xs
    tipS : (y : b) → y ≡ h xs                    → B' (suc k) (suc k) b h xs
    bin  : B' n (suc k) b         h           xs
         → B' n      k  b (λ zs → h (x ∷ zs)) xs → B' (suc n) (suc k) b h (x ∷ xs)

  -- testB' : {b : Set} {h : Vec Char 2 → b} → B' 4 2 b h ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
  -- testB' = bin (bin (tipS {!   !} {!   !})
  --                   (bin (tipS {!   !} {!   !})
  --                        (tipZ {!   !} {!   !})))
  --              (bin (bin (tipS {!   !} {!   !})
  --                        (tipZ {!   !} {!   !}))
  --                   (tipZ {!   !} {!   !}))

  -- end of module RestrictedSpecification

data BT : (n k : ℕ) → (Vec a k → Set) → Vec a n → Set where
  tipZ : p []                               → BT n        zero   p xs
  tipS : p xs                               → BT (suc k) (suc k) p xs
  bin  : BT n (suc k)        p           xs
       → BT n      k (λ zs → p (x ∷ zs)) xs → BT (suc n) (suc k) p (x ∷ xs)

-- testBT : {p : Vec Char 2 → Set} → BT 4 2 p ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ [])
-- testBT = bin (bin (tipS {!   !})
--                   (bin (tipS {!   !})
--                        (tipZ {!   !})))
--              (bin (bin (tipS {!   !})
--                        (tipZ {!   !}))
--                   (tipZ {!   !}))

--------
-- Section 2.3

bounded : BT n k p xs → k ≤ n
bounded (tipZ _)  = z≤n
bounded (tipS _)  = ≤-refl
bounded (bin _ u) = s≤s (bounded u)

unbounded : BT k (suc k) p xs → ⊥
unbounded (bin t u) = unbounded u

mapBT : (∀ {ys} → p ys → q ys) → ∀ {xs} → BT n k p xs → BT n k q xs
mapBT f (tipZ x)  = tipZ (f x)
mapBT f (tipS x)  = tipS (f x)
mapBT f (bin t u) = bin (mapBT f t) (mapBT f u)

unTip : BT n n p xs → p xs
unTip           (tipS x)  = x
unTip {xs = []} (tipZ x)  = x
unTip           (bin t _) = ⊥-elim (unbounded t)

zipBTWith : (∀ {ys} → p ys → q ys → r ys) → ∀ {xs} → BT n k p xs → BT n k q xs → BT n k r xs
zipBTWith f (tipZ x)   (tipZ y)   = tipZ (f x y)
zipBTWith f (tipS x)   u          = tipS (f x (unTip u))
zipBTWith f (bin t _ ) (tipS _)   = ⊥-elim (unbounded t)
zipBTWith f (bin t t') (bin u u') = bin (zipBTWith f t u) (zipBTWith f t' u')

_∷ᴮᵀ_ : p xs → BT (1 + k) k (p ∘ (x ∷_)) xs → BT (2 + k) (1 + k) p (x ∷ xs)
p ∷ᴮᵀ t = bin (tipS p) t

retabulate : k < n → BT n k p xs → BT n (1 + k) (BT (1 + k) k p) xs
retabulate            1+k<1+k (tipS _)                  = ⊥-elim (<-irrefl refl 1+k<1+k)
retabulate {xs = _ ∷ []   } _ (tipZ y)                  = tipS (tipZ y)
retabulate {xs = _ ∷ _ ∷ _} _ (tipZ y)                  = bin (retabulate (s≤s z≤n) (tipZ y)) (tipZ (tipZ y))
retabulate _             (bin   (tipS y  ) u          ) = tipS (y ∷ᴮᵀ u)
retabulate _             (bin t@(bin t' _)   (tipZ z )) = bin (retabulate (s≤s (bounded t')) t) (mapBT (_∷ᴮᵀ (tipZ z)) t)
retabulate 2+n<2+n       (bin   (bin _  _)   (tipS _ )) = ⊥-elim (<-irrefl refl 2+n<2+n)
retabulate (s≤s 1+k<1+n) (bin t@(bin t' _) u@(bin _ _)) = bin (retabulate (s≤s (bounded t')) t) (zipBTWith _∷ᴮᵀ_ t (retabulate 1+k<1+n u))

--------
-- Section 2.4

incr : suc m ≤′ n → m ≤′ n
incr  ≤′-refl    = ≤′-step ≤′-refl
incr (≤′-step d) = ≤′-step (incr d)

module Choose where

  data Exactly : a → Set where
    exactly : (x : a) → Exactly x

  mapExactly : (f : a → b) → Exactly x → Exactly (f x)
  mapExactly f (exactly x) = exactly (f x)

  choose : (n k : ℕ) → k ≤′ n → (xs : Vec a n) → BT n k Exactly xs
  choose _        zero   _           _        = tipZ (exactly [])
  choose (suc k) (suc k)  ≤′-refl    xs       = tipS (exactly xs)
  choose (suc n) (suc k) (≤′-step d) (x ∷ xs) = bin (choose n (suc k) d xs) (mapBT (mapExactly (x ∷_)) (choose n k (incr d) xs))

  toBTExactly : BT n k (const ⊤) xs → BT n k Exactly xs
  toBTExactly = mapBT (λ { {ys} tt → exactly ys })

  -- end of module Choose

blank' : (n k : ℕ) → k ≤′ n → {xs : Vec a n} → BT n k (const ⊤) xs
blank' _        zero   _                   = tipZ tt
blank' (suc k) (suc k)  ≤′-refl            = tipS tt
blank' (suc n) (suc k) (≤′-step d) {_ ∷ _} = bin (blank' n (suc k) d) (blank' n k (incr d))

module Monster where

  ImmediateSublistInduction : Set₁
  ImmediateSublistInduction =
    {a : Set} (s  : ∀ {k} → Vec a k → Set)
              (e  : s [])
              (g  : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys)
    {n : ℕ}   (xs : Vec a n) → s xs

  td : ImmediateSublistInduction
  td s e g {zero } [] = e
  td s e g {suc n} ys = g (mapBT (λ { {ys} tt → td s e g {n} ys}) (blank' (1 + n) n (≤′-step ≤′-refl)))

  -- end of module Monster

blank : (n k : ℕ) → k ≤′ n → {xs : Vec a n} → ⊤ → BT n k (const ⊤) xs
blank n k k≤n = const (blank' n k k≤n)

ImmediateSublistInduction : Set₁
ImmediateSublistInduction =
  {a : Set} (s : ∀ {k} → Vec a k → Set)
            (e : {ys : Vec a 0} → ⊤ → s ys)
            (g : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys)
            (n : ℕ) {xs : Vec a n} → ⊤ → s xs

td : ImmediateSublistInduction
td s e g  zero   = e
td s e g (suc n) = g ∘ mapBT (td s e g n) ∘ blank (1 + n) n (≤′-step ≤′-refl)

-- bu : ImmediateSublistInduction
-- bu s e g n = unTip ∘ loop 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)
--   where
--     loop : (k : ℕ) → k ≤‴ n → BT n k s xs → BT n n s xs
--     loop n  ≤‴-refl    = id
--     loop k (≤‴-step d) = loop (1 + k) d ∘ mapBT g ∘ retabulate (≤‴⇒≤ d)

bu-loop : {s : ∀ {k} → Vec a k → Set} (g : ∀ {k} → {ys : Vec a (1 + k)} → BT (1 + k) k s ys → s ys) {n : ℕ}
          (k : ℕ) → k ≤‴ n → {xs : Vec a n} → BT n k s xs → BT n n s xs
bu-loop g n  ≤‴-refl    = id
bu-loop g k (≤‴-step d) = bu-loop g (1 + k) d ∘ mapBT g ∘ retabulate (≤‴⇒≤ d)

bu : ImmediateSublistInduction
bu s e g n = unTip ∘ bu-loop g 0 (≤⇒≤‴ z≤n) ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)

--------
-- Section 2.5

module ℕ-InductionPrinciple where

  ℕ-Induction : Set₁
  ℕ-Induction = (p  : ℕ → Set)
                (pz : p zero)
                (ps : ∀ {m} → p m → p (suc m))
                (n  : ℕ) → p n

  ind : ℕ-Induction
  ind P pz ps  zero   = pz
  ind P pz ps (suc n) = ps (ind P pz ps n)

  ℕ-Induction-unary-parametricity : ℕ-Induction → Set₁
  ℕ-Induction-unary-parametricity f =
      {p  : ℕ → Set}                 (q : ∀ {m} → p m → Set)
    → {pz : p zero}                  (qz : q pz)
    → {ps : ∀ {m} → p m → p (suc m)} (qs : ∀ {m} {x : p m} → q x → q (ps x))
    → {n  : ℕ} → q (f p pz ps n)

  ℕ-Induction-uniqueness-from-parametricity :
      (f : ℕ-Induction) → ℕ-Induction-unary-parametricity f
    → (P : ℕ → Set) (pz : P zero) (ps : ∀ {m} → P m → P (suc m)) (n : ℕ)
    → f P pz ps n ≡ ind P pz ps n
  ℕ-Induction-uniqueness-from-parametricity f param p pz ps n =
    param (λ {m} x → x ≡ ind p pz ps m) refl (cong ps)

  -- end of module ℕ-InductionPrinciple

BT' : ({ys : Vec a k} → p ys → Set) → BT n k p xs → Set
BT' q (tipZ x)  = q x
BT' q (tipS x)  = q x
BT' q (bin t u) = BT' q t × BT' q u

ISI-unary-parametricity : ImmediateSublistInduction → Set₁
ISI-unary-parametricity f =
  {a : Set} {s : ∀ {k} → Vec a k → Set}               (s' : ∀ {k} {ys : Vec a k} → s ys → Set)
            {e : {ys : Vec a 0} → ⊤ → s ys}           (e' : ∀ {ys} → s' (e {ys} tt))
            {g : ∀ {k ys} → BT (1 + k) k s ys → s ys} (g' : ∀ {k ys} {t : BT (1 + k) k s ys} → BT' s' t → s' (g t))
            {n : ℕ} {xs : Vec a n} → s' (f s e g n {xs} tt)

ISI-uniqueness-from-parametricity :
    (f : ImmediateSublistInduction) → ISI-unary-parametricity f
  → {a : Set} (s : ∀ {k} → Vec a k → Set)
  → (e : {ys : Vec a 0} → ⊤ → s ys) (g : ∀ {k ys} → BT (1 + k) k s ys → s ys) (n : ℕ) {xs : Vec a n}
  → f s e g n {xs} tt ≡ td s e g n {xs} tt
ISI-uniqueness-from-parametricity f param {a} s e g n =
  param (λ {m} {ys} x → x ≡ td s e g m {ys} tt) refl (λ t' → cong g (see-below s (λ xs → td s e g _ {xs} tt) _ t'))
  where
    see-below : (ss : Vec a k → Set) (h : (xs : Vec a k) → ss xs)
              → (ss' : BT (1 + k) k ss xs) → BT' (λ {ys} x → x ≡ h ys) ss'
              → ss' ≡ mapBT (λ {ys} _ → h ys) (blank' (suc k) k (≤′-step ≤′-refl))
    see-below ss h (tipZ _)          eq        = cong tipZ eq
    see-below ss h (bin (tipS _) t) (eq , ss') = cong₂ bin (cong tipS eq) (see-below (ss ∘ (_ ∷_)) (h ∘ (_ ∷_)) t ss')
    see-below ss h (bin (bin t _) _) _         = ⊥-elim (unbounded t)

--------
-- Section 3.1

Fam : Set → Set₁
Fam a = a → Set

_⇉_ : Fam a → Fam a → Set
p ⇉ q = ∀ {x} → p x → q x

infix 2 _⇉_

--------
-- Section 3.2

IsProp : Set → Set
IsProp a = {x y : a} → x ≡ y

IsProp' : Set → Set
IsProp' a = (x y : a) → x ≡ y

BT-isProp' : (∀ {ys} → IsProp (p ys)) → IsProp' (BT n k p xs)
BT-isProp' p-isProp (tipZ _)  (tipZ _)    = cong tipZ p-isProp
BT-isProp' p-isProp (tipS _)  (tipS _)    = cong tipS p-isProp
BT-isProp' p-isProp (bin t u) (bin t' u') = cong₂ bin (BT-isProp' p-isProp t t') (BT-isProp' p-isProp u u')
BT-isProp' p-isProp (tipS _)  (bin t' _)  = ⊥-elim (unbounded t')
BT-isProp' p-isProp (bin t _) (tipS _)    = ⊥-elim (unbounded t)

BT-isProp : (∀ {ys} → IsProp (p ys)) → IsProp (BT n k p xs)
BT-isProp p-isProp = BT-isProp' p-isProp _ _

rotation : ∀ {k<n k≤n k≤1+k 1+k≤n}
         → retabulate k<n (blank n k k≤n {xs} tt) ≡ mapBT (blank (1 + k) k k≤1+k) (blank n (1 + k) 1+k≤n tt)
rotation = BT-isProp (BT-isProp refl)

--------
-- ‘Whining, I finish the entire proof in Agda.’

-- more categorical definitions

-- families of functions with an explicit index type
∀[_]_⇉_ : (a : Set) → Fam a → Fam a → Set
∀[ a ] p ⇉ q = p ⇉ q

infix 2 ∀[_]_⇉_

-- exponential objects in Fam categories
_⇒_ : Fam a → Fam a → Fam a
(p ⇒ q) x = p x → q x

-- table construction phases

tdRec : (n : ℕ) → Fam (Vec a n)
tdRec  zero   = const ⊤
tdRec (suc n) = BT (suc n) n (tdRec n)

td-construct : (n : ℕ) → ∀[ Vec a n ] const ⊤ ⇉ tdRec n
td-construct  zero   = id
td-construct (suc n) = mapBT (td-construct n) ∘ blank (suc n) n (≤′-step ≤′-refl)

buRec : k ≤‴ n → Fam (Vec a k) → Fam (Vec a n)
buRec          ≤‴-refl    = id
buRec {k = k} (≤‴-step d) = buRec d ∘ BT (suc k) k

bu-construct-loop : (k≤n : k ≤‴ n) → BT n k p ⇉ BT n n (buRec k≤n p)
bu-construct-loop  ≤‴-refl    = id
bu-construct-loop (≤‴-step d) = bu-construct-loop d ∘ retabulate (≤‴⇒≤ d)

bu-construct : (n : ℕ) → ∀[ Vec a n ] const ⊤ ⇉ buRec (≤⇒≤‴ z≤n) (const ⊤)
bu-construct n = unTip ∘ bu-construct-loop (≤⇒≤‴ z≤n) ∘ blank n 0 (≤⇒≤′ z≤n)

-- functoriality

cong-mapBT : {f g : p ⇉ q} → (∀ {ys} (x : p ys) → f x ≡ g x)
           → (t : BT n k p xs) → mapBT f t ≡ mapBT g t
cong-mapBT f≗g (tipZ x)  = cong tipZ (f≗g x)
cong-mapBT f≗g (tipS x)  = cong tipS (f≗g x)
cong-mapBT f≗g (bin t u) = cong₂ bin (cong-mapBT f≗g t) (cong-mapBT f≗g u)

mapBT-∘ : (f : q ⇉ r) (g : p ⇉ q)
        → (t : BT n k p xs) → mapBT (f ∘ g) $ t ≡ mapBT f ∘ mapBT g $ t
mapBT-∘ f g (tipZ _)  = refl
mapBT-∘ f g (tipS _)  = refl
mapBT-∘ f g (bin t u) = cong₂ bin (mapBT-∘ f g t) (mapBT-∘ f g u)

map-buRec : (k≤n : k ≤‴ n) → p ⇉ q → buRec k≤n p ⇉ buRec k≤n q
map-buRec  ≤‴-refl    f = f
map-buRec (≤‴-step d) f = map-buRec d (mapBT f)

cong-map-buRec :
    (k≤n : k ≤‴ n) {f g : p ⇉ q} → (∀ {ys} (p : p ys) → f p ≡ g p)
  → {xs : Vec a n} (t : buRec k≤n p xs) → map-buRec k≤n f t ≡ map-buRec k≤n g t
cong-map-buRec  ≤‴-refl    f≗g t = f≗g t
cong-map-buRec (≤‴-step d) f≗g t = cong-map-buRec d (cong-mapBT f≗g) t

map-buRec-∘ : (k≤n : k ≤‴ n) (f : q ⇉ r) (g : p ⇉ q)
            → {xs : Vec a n} (t : buRec k≤n p xs)
            → map-buRec k≤n (f ∘ g) $ t ≡ map-buRec k≤n f ∘ map-buRec k≤n g $ t
map-buRec-∘  ≤‴-refl    f g t = refl
map-buRec-∘ (≤‴-step d) f g t =
  trans (cong-map-buRec d (mapBT-∘ f g) t) (map-buRec-∘ d (mapBT f) (mapBT g) t)

-- propositionality

≤-isProp' : {m n : ℕ} → IsProp' (m ≤ n)
≤-isProp'  z≤n       z≤n       = refl
≤-isProp' (s≤s m≤n) (s≤s m≤n') = cong s≤s (≤-isProp' m≤n m≤n')

≤-isProp : {m n : ℕ} → IsProp (m ≤ n)
≤-isProp = ≤-isProp' _ _

tdRec-isProp : (n : ℕ) {xs : Vec a n} → IsProp (tdRec n xs)
tdRec-isProp  zero   = refl
tdRec-isProp (suc n) = BT-isProp (tdRec-isProp n)

-- naturality

unTip-natural : (h : p ⇉ q) {xs : Vec a n} (t : BT n n p xs)
              → h ∘ unTip $ t ≡ unTip ∘ mapBT h $ t
unTip-natural h      (tipS p)  = refl
unTip-natural h {[]} (tipZ p)  = refl
unTip-natural h      (bin t _) = ⊥-elim (unbounded t)

zipBTWith-natural :
    (P : p ⇉ p') (Q : q ⇉ q') (R : r ⇉ r')
    (f : p ⇉ q ⇒ r) (f' : p' ⇉ q' ⇒ r')
  → ({xs : Vec a k} {x : p xs} {y : q xs} → R (f x y) ≡ f' (P x) (Q y))
  →  {xs : Vec a n} (t : BT n k p xs) (u : BT n k q xs)
  → mapBT R (zipBTWith f t u) ≡ zipBTWith f' (mapBT P t) (mapBT Q u)
zipBTWith-natural P Q R f f' f∼f' (tipZ x)   (tipZ y)   = cong tipZ f∼f'
zipBTWith-natural P Q R f f' f∼f' (tipS x)   u          = cong tipS (trans f∼f' (cong (f' (P x)) (unTip-natural Q u)))
zipBTWith-natural P Q R f f' f∼f' (bin t _)  (tipS _)   = ⊥-elim (unbounded t)
zipBTWith-natural P Q R f f' f∼f' (bin t t') (bin u u') = cong₂ bin (zipBTWith-natural P Q R f f' f∼f' t  u )
                                                                    (zipBTWith-natural P Q R f f' f∼f' t' u')

retabulate-natural : (k<n : k < n) {xs : Vec a n} (h : p ⇉ q) (t : BT n k p xs)
                   → mapBT (mapBT h) ∘ retabulate k<n $ t ≡ retabulate k<n ∘ mapBT h $ t
retabulate-natural 1+n<1+n       h (tipS p)                       = ⊥-elim (<-irrefl refl 1+n<1+n)
retabulate-natural _ {_ ∷ []   } h (tipZ p)                       = refl
retabulate-natural _ {_ ∷ _ ∷ _} h (tipZ p)                       = cong₂ bin (retabulate-natural (s≤s z≤n) h (tipZ p)) refl
retabulate-natural _             h (bin   (tipS p)   u)           = refl
retabulate-natural _             h (bin t@(bin t' _)   (tipZ q))  = cong₂ bin (trans (retabulate-natural (s≤s (bounded t')) h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (sym (mapBT-∘ (mapBT h) (_∷ᴮᵀ (tipZ q)) t)) (mapBT-∘ (_∷ᴮᵀ (tipZ (h q))) h t))
retabulate-natural _             h (bin t@(bin _  _)   (tipS q))  = ⊥-elim (unbounded t)
retabulate-natural (s≤s 1+k<1+n) h (bin t@(bin t' _) u@(bin _ _)) = cong₂ bin (trans (retabulate-natural (s≤s (bounded t')) h t) (cong (λ ineq → retabulate ineq (mapBT h t)) ≤-isProp)) (trans (zipBTWith-natural h (mapBT h) (mapBT h) _∷ᴮᵀ_ _∷ᴮᵀ_ refl t (retabulate 1+k<1+n u)) (cong (zipBTWith _∷ᴮᵀ_ (mapBT h t)) (retabulate-natural 1+k<1+n h u)))

bu-construct-loop-natural :
    (k≤n : k ≤‴ n) (h : p ⇉ q) {xs : Vec a n} (t : BT n k p xs)
  → mapBT (map-buRec k≤n h) ∘ bu-construct-loop k≤n $ t ≡ bu-construct-loop k≤n ∘ mapBT h $ t
bu-construct-loop-natural  ≤‴-refl    h t = refl
bu-construct-loop-natural (≤‴-step d) h t =
  begin
    mapBT (map-buRec (≤‴-step d) h) ∘ bu-construct-loop (≤‴-step d)           $ t
      ≡⟨ refl ⟩
    mapBT (map-buRec d (mapBT h)) ∘ bu-construct-loop d ∘ retabulate (≤‴⇒≤ d) $ t
      ≡⟨ bu-construct-loop-natural d (mapBT h) _ ⟩
    bu-construct-loop d ∘ mapBT (mapBT h) ∘ retabulate (≤‴⇒≤ d)               $ t
      ≡⟨ cong (bu-construct-loop d) (retabulate-natural (≤‴⇒≤ d) h t) ⟩
    bu-construct-loop d ∘ retabulate (≤‴⇒≤ d) ∘ mapBT h                       $ t
      ≡⟨ refl ⟩
    bu-construct-loop (≤‴-step d) ∘ mapBT h                                   $ t
  ∎
  where open ≡-Reasoning

unTip∘bu-construct-loop-natural :
    (k≤n : k ≤‴ n) (h : p ⇉ q) {xs : Vec a n} (t : BT n k p xs)
  → map-buRec k≤n h ∘ unTip ∘ bu-construct-loop k≤n           $ t
  ≡                   unTip ∘ bu-construct-loop k≤n ∘ mapBT h $ t
unTip∘bu-construct-loop-natural k≤n h t =
  begin
    map-buRec k≤n h ∘ unTip ∘ bu-construct-loop k≤n         $ t
      ≡⟨ unTip-natural (map-buRec k≤n h) (bu-construct-loop k≤n t) ⟩
    unTip ∘ mapBT (map-buRec k≤n h) ∘ bu-construct-loop k≤n $ t
      ≡⟨ cong unTip (bu-construct-loop-natural k≤n h _) ⟩
    unTip ∘ bu-construct-loop k≤n ∘ mapBT h                 $ t
  ∎
  where open ≡-Reasoning

-- overall structure of the equality proof
overall : {a a' b : Set}
        → (f : a → b) (f' : a' → b)
        → ((Σ[ c ∈ Set ] (c → b)) ∋ (a , f)) ≡ (a' , f')
        → IsProp a
        → (x : a) (x' : a') → f x ≡ f' x'
overall f .f refl a-isProp _ _ = cong f a-isProp

module DemolitionAndEquality
  {a : Set} (s : ∀ {k} → Fam (Vec a k))
  (e : const ⊤ ⇉ s {0}) (g : ∀ {k} → BT (1 + k) k s ⇉ s)
  where

  -- table demolition phases

  td-demolish : (n : ℕ) → tdRec n ⇉ s
  td-demolish  zero   = e
  td-demolish (suc n) = g ∘ mapBT (td-demolish n)

  bu-demolish-loop : (k≤n : k ≤‴ n) → buRec k≤n s ⇉ s
  bu-demolish-loop  ≤‴-refl    = id
  bu-demolish-loop (≤‴-step d) = bu-demolish-loop d ∘ map-buRec d g

  bu-demolish : (n : ℕ) → ∀[ Vec a n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ s
  bu-demolish n = bu-demolish-loop 0≤n ∘ map-buRec 0≤n e
    where 0≤n = ≤⇒≤‴ z≤n

  -- separation into two phases

  td-separation : (n : ℕ) {xs : Vec a n}
                → td s e g n {xs} $ tt ≡ td-demolish n ∘ td-construct n $ tt
  td-separation  zero   = refl
  td-separation (suc n) =
    begin
      td s e g (suc n)                                                                       $ tt
        ≡⟨ refl ⟩
      g ∘ mapBT (td s e g n) ∘ blank (suc n) n (≤′-step ≤′-refl)                             $ tt
        ≡⟨ cong g (cong-mapBT (λ _ → td-separation n) _) ⟩
      g ∘ mapBT (td-demolish n ∘ td-construct n) ∘ blank (suc n) n (≤′-step ≤′-refl)         $ tt
        ≡⟨ cong g (mapBT-∘ (td-demolish n) (td-construct n) _) ⟩
      g ∘ mapBT (td-demolish n) ∘ mapBT (td-construct n) ∘ blank (suc n) n (≤′-step ≤′-refl) $ tt
        ≡⟨ refl ⟩
      td-demolish (suc n) ∘ td-construct (suc n)                                             $ tt
    ∎
    where open ≡-Reasoning

  bu-loop-separation :
      (k≤n : k ≤‴ n)
    → {xs : Vec a n} (t : BT n k s xs)
    → unTip ∘ bu-loop g k k≤n $ t ≡ bu-demolish-loop k≤n ∘ unTip ∘ bu-construct-loop k≤n $ t
  bu-loop-separation  ≤‴-refl    t = refl
  bu-loop-separation (≤‴-step d) t =
    begin
      unTip ∘ bu-loop g _ (≤‴-step d)                                                        $ t
        ≡⟨ refl ⟩
      unTip ∘ bu-loop g _ d ∘ mapBT g ∘ retabulate (≤‴⇒≤ d)                                  $ t
        ≡⟨ bu-loop-separation d _ ⟩
      bu-demolish-loop d ∘ unTip ∘ bu-construct-loop d ∘ mapBT g ∘ retabulate (≤‴⇒≤ d)       $ t
        ≡⟨ cong (bu-demolish-loop d) (sym (unTip∘bu-construct-loop-natural d g _)) ⟩
      bu-demolish-loop d ∘ map-buRec d g ∘ unTip ∘ bu-construct-loop d ∘ retabulate (≤‴⇒≤ d) $ t
        ≡⟨ refl ⟩
      bu-demolish-loop (≤‴-step d) ∘ unTip ∘ bu-construct-loop (≤‴-step d)                   $ t
    ∎
    where open ≡-Reasoning

  bu-separation : (n : ℕ) {xs : Vec a n} → bu s e g n {xs} $ tt ≡ bu-demolish n ∘ bu-construct n $ tt
  bu-separation n =
    begin
      bu s e g n                                                                                    $ tt
        ≡⟨ refl ⟩
      unTip ∘ bu-loop g _ 0≤n ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)                                      $ tt
        ≡⟨ bu-loop-separation 0≤n _ ⟩
      bu-demolish-loop 0≤n ∘ unTip ∘ bu-construct-loop 0≤n ∘ mapBT e ∘ blank n 0 (≤⇒≤′ z≤n)         $ tt
        ≡⟨ cong (bu-demolish-loop 0≤n) (sym (unTip∘bu-construct-loop-natural 0≤n e _)) ⟩
      bu-demolish-loop 0≤n ∘ map-buRec 0≤n e ∘ unTip ∘ bu-construct-loop 0≤n ∘ blank n 0 (≤⇒≤′ z≤n) $ tt
        ≡⟨ refl ⟩
      bu-demolish n ∘ bu-construct n                                                                $ tt
    ∎
    where 0≤n = ≤⇒≤‴ z≤n
          open ≡-Reasoning

  -- equality between the table demolition phases

  -- an alternative form that can be proved equal to td-demolish without using functoriality
  bu-demolish-loop' : (k≤n : k ≤‴ n) → r ⇉ s → buRec k≤n r ⇉ s
  bu-demolish-loop'  ≤‴-refl    h = h
  bu-demolish-loop' (≤‴-step d) h = bu-demolish-loop' d (g ∘ mapBT h)

  bu-demolish' : (n : ℕ) → ∀[ Vec a n ] buRec (≤⇒≤‴ z≤n) (const ⊤) ⇉ s
  bu-demolish' n = bu-demolish-loop' (≤⇒≤‴ z≤n) e

  bu-demolish-loop-equiv :
      (k≤n : k ≤‴ n) (h : r ⇉ s) {xs : Vec a n} (t : buRec k≤n r xs)
    → bu-demolish-loop' k≤n h $ t ≡ bu-demolish-loop k≤n ∘ map-buRec k≤n h $ t
  bu-demolish-loop-equiv  ≤‴-refl    h t = refl
  bu-demolish-loop-equiv (≤‴-step d) h t =
    begin
      bu-demolish-loop' (≤‴-step d) h                            $ t
        ≡⟨ refl ⟩
      bu-demolish-loop' d (g ∘ mapBT h)                          $ t
        ≡⟨ bu-demolish-loop-equiv d (g ∘ mapBT h) _ ⟩
      bu-demolish-loop d ∘ map-buRec d (g ∘ mapBT h)             $ t
        ≡⟨ cong (bu-demolish-loop d) (map-buRec-∘ d g (mapBT h) _) ⟩
      bu-demolish-loop d ∘ map-buRec d g ∘ map-buRec d (mapBT h) $ t
        ≡⟨ refl ⟩
      bu-demolish-loop (≤‴-step d) ∘ map-buRec (≤‴-step d) h     $ t
    ∎
    where open ≡-Reasoning

  bu-demolish-equiv :
      (n : ℕ) {xs : Vec a n} (t : buRec (≤⇒≤‴ z≤n) (const ⊤) xs)
    → bu-demolish' n t ≡ bu-demolish n t
  bu-demolish-equiv n = bu-demolish-loop-equiv (≤⇒≤‴ z≤n) e

  td≗bu-demolish :
      (k≤n : k ≤‴ n) {xs : Vec a n}
    → ((Σ[ b ∈ Set ] (b → s xs))
      ∋ (tdRec n xs             , td-demolish n))
      ≡ (buRec k≤n (tdRec k) xs , bu-demolish-loop' k≤n (td-demolish k))
  td≗bu-demolish  ≤‴-refl    = refl
  td≗bu-demolish (≤‴-step d) = td≗bu-demolish d

  -- equality between the top-down and bottom-up algorithms

  td≗bu : (n : ℕ) {xs : Vec a n} → td s e g n {xs} $ tt ≡ bu s e g n $ tt
  td≗bu n =
    begin
      td s e g n                      $ tt
        ≡⟨ td-separation n ⟩
      td-demolish n ∘ td-construct n  $ tt
        ≡⟨ overall (td-demolish n) (bu-demolish-loop' 0≤n e) (td≗bu-demolish 0≤n)
             (tdRec-isProp n) (td-construct n tt) (bu-construct n tt) ⟩
      bu-demolish' n ∘ bu-construct n $ tt
        ≡⟨ bu-demolish-equiv n _ ⟩
      bu-demolish n ∘ bu-construct n  $ tt
        ≡⟨ sym (bu-separation n) ⟩
      bu s e g n                      $ tt
    ∎
    where 0≤n = ≤⇒≤‴ z≤n
          open ≡-Reasoning

  -- end of module DemolitionAndEquality

-- ‘But as usual, in the end there’s a dopamine hit from seeing everything checked.’

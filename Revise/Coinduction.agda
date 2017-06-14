module Revise.Coinduction where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Stream₀ : Set → Set
Stream₀ A = ℕ → A

open import Coinduction using (∞; ♯_; ♭)

data Stream (A : Set) : Set where
  _∷_ : (x : A) → (xs : ∞ (Stream A)) → Stream A

infixr 5 _∷_

data ℕω : Set where
  zero : ℕω
  suc : ∞ ℕω → ℕω

data ℕ⁻ : Set where
  suc : ℕ⁻ → ℕ⁻

data Ω : Set where
  suc : ∞ Ω → Ω

ω : ℕω
ω = suc (♯ ω)

head : ∀ {A} → Stream A → A
head (x ∷ xs) = x

tail : ∀ {A} → Stream A → Stream A
tail (x ∷ xs) = ♭ xs

lookup : ∀ {A} → ℕ → Stream A → A
lookup zero (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

take : ∀ {A} (n : ℕ) → Stream A → Vec A n
take zero xs = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

drop : ∀ {A} → ℕ → Stream A → Stream A
drop zero xs = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

repeat : ∀ {A} → A → Stream A
repeat x = x ∷ ♯ repeat x

iterate : ∀ {A} → (A → A) → A → Stream A
iterate f x = x ∷ ♯ iterate f (f x)

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

zipWith : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys)

-- curlyvee
_⋎_ : ∀ {A} → Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ (♭ xs))

infixr 5 _⋎_

data Colist (A : Set) : Set where
  [] : Colist A
  _∷_ : A → ∞ (Colist A) → Colist A

toColist : ∀ {A} → Stream A → Colist A
toColist (x ∷ xs) = x ∷ ♯ toColist (♭ xs)

_++_ : ∀ {A} → Colist A → Stream A → Stream A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

infixr 5 _++_

data _≈_ {A : Set} : Stream A → Stream A → Set where
  _∷_ : (x : A) {xs ys : ∞ (Stream A)} → ∞ (♭ xs ≈ ♭ ys) → x ∷ xs ≈ x ∷ ys

infix 4 _≈_

0s≉1s : ∀ {s} → 0 ∷ s ≈ 1 ∷ s → ⊥
0s≉1s ()

r0≈r0 : repeat 0 ≈ repeat 0
r0≈r0 = 0 ∷ ♯ r0≈r0

≈-refl : ∀ {A} {xs : Stream A} → xs ≈ xs
≈-refl {xs = x ∷ _} = x ∷ ♯ ≈-refl

≈-sym : ∀ {A} {xs ys : Stream A} → xs ≈ ys → ys ≈ xs
≈-sym (x ∷ xs) = x ∷ ♯ ≈-sym (♭ xs)

≈-trans : ∀ {A} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans (x ∷ xs) (_ ∷ ys) = x ∷ ♯ ≈-trans (♭ xs) (♭ ys)

map-cong : ∀ {A B} (f : A → B) {xs ys : Stream A} → xs ≈ ys → map f xs ≈ map f ys
map-cong f (x ∷ xs) = f x ∷ ♯ map-cong f (♭ xs)

elem-≡ : ∀ {A} {xs ys : Stream A} → xs ≈ ys → (n : ℕ) → lookup n xs ≡ lookup n ys
elem-≡ (x ∷ xs) zero = refl
elem-≡ (x ∷ xs) (suc n) = elem-≡ (♭ xs) n

-- func-≡ : ∀ {A} (f : Stream A → ℕ) (xs ys : Stream A) → xs ≈ ys → f xs ≡ f ys
-- this implys an ability to check infinite comparison

data _∈_ {A : Set} : A → Stream A → Set where
  here : {x : A} {xs : ∞ (Stream A)} → x ∈ x ∷ xs
  there : {x y : A} {xs : ∞ (Stream A)} → (x ∈ ♭ xs) → x ∈ y ∷ xs

infix 4 _∈_

-- sqsubseteq, squb=
data _⊑_ {A : Set} : Colist A → Stream A → Set where
  [] : {ys : Stream A} → [] ⊑ ys
  _∷_ : {x : A} {xs : ∞ (Colist A)} {ys : ∞ (Stream A)} → ∞ (♭ xs ⊑ ♭ ys) → x ∷ xs ⊑ x ∷ ys

infix 4 _⊑_

data SP (A B : Set) : Set where
  get : (A → SP A B) → SP A B
  put : B → ∞ (SP A B) → SP A B

eat : ∀ {A B} → SP A B → Stream A → Stream B
eat (get f) (y ∷ xs) = eat (f y) (♭ xs)
eat (put x xs) ys = x ∷ ♯ eat (♭ xs) ys

_∘_ : ∀ {A B C} → SP B C → SP A B → SP A C
p ∘ get g = get (λ x → p ∘ g x)
get f ∘ put y ys = f y ∘ ♭ ys
put x xs ∘ q = put x (♯ (♭ xs ∘ q))

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

-- ℕ′ : Set
-- ℕ′ = ⊤ ⊎ Rec (♯ ℕ′)

module Revise.Reflection where

open import Data.Nat using (ℕ; _+_; suc; zero; _≤_; s≤s; z≤n; _≟_)
open import Data.Vec using (Vec; []; _∷_; tail; head)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function renaming (_∘_ to _∘f_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

ex : {A : Set} → (A → Set) → Set
ex = Σ _

syntax ex (λ y → x) = y ∣ x

module _ {A : Set} where

  private V = Vec A

  infix 1 _~_
  infixl 3 _∘_

  data _~_ : ∀ {n} → V n → V n → Set where
    zero : [] ~ []
    suc : ∀ {n a} {xs ys : V n} → xs ~ ys → a ∷ xs ~ a ∷ ys
    _∘_ : ∀ {n} {xs ys zs : V n} → xs ~ ys → ys ~ zs → xs ~ zs
    exch : ∀ {n a b} {xs : V n} → a ∷ b ∷ xs ~ b ∷ a ∷ xs

  ~-refl : ∀ {n} {xs : V n} → xs ~ xs
  ~-refl {xs = []} = zero
  ~-refl {xs = x ∷ []} = suc zero
  ~-refl {xs = x ∷ x₁ ∷ xs} = exch ∘ exch

  ~-sym : ∀ {n} {xs ys : V n} → xs ~ ys → ys ~ xs
  ~-sym zero = zero
  ~-sym (suc x) = suc (~-sym x)
  ~-sym (x ∘ x₁) = ~-sym x₁ ∘ ~-sym x
  ~-sym exch = exch

  _∘simp_ : ∀ {n} {xs ys zs : V n} → xs ~ ys → ys ~ zs → xs ~ zs
  zero ∘simp y = y
  suc zero ∘simp y = y
  (exch ∘ exch) ∘simp y = y
  x ∘simp (exch ∘ exch) = x
  x ∘simp y = x ∘ y

  sucSimp : ∀ {n x} {xs ys : V n} → xs ~ ys → x ∷ xs ~ x ∷ ys
  sucSimp (suc zero) = exch ∘ exch
  sucSimp (exch ∘ exch) = exch ∘ exch
  sucSimp x = suc x

  infix 1 _≋_ _≈_
  infixr 3 _↪_
  infixr 4 _∷_

  data Into (n : ℕ) : Set where
    _↪_ : A → V n → Info n

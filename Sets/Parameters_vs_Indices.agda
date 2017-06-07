module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set} (x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

data _⊆_ {A : Set} : List A → List A → Set where
  null : ∀ {xs} → [] ⊆ xs
  elem : ∀ {x ys xs} → ys ⊆ xs → x ∈ xs → x ∷ ys ⊆ xs

infix 4 _⊆_

prop₁ : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
prop₁ = elem (elem null (later first)) first

prop₂ : 1 ∷ 2 ∷ 3 ∷ [] ⊆ 1 ∷ 2 ∷ [] → ⊥
prop₂ (elem (elem (elem null (later (later ()))) x₂) x₃)

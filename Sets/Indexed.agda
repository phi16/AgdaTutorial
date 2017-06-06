module Sets.Indexed where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc : (n : ℕ) → Fin n → Fin (suc n)

data Bool↓ : Bool → Set where
  only : Bool↓ true

data ℕ↓ : ℕ → Set where
  null : ℕ↓ 0
  even : (n : ℕ) → ℕ↓ n → ℕ↓ (suc (suc n))

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

po : Vec Bool 2
po = cons 1 false (cons 0 true [])

data Switch (A B : Set) : Bool → Set where
  withA : A → Switch A B false
  withB : B → Switch A B true

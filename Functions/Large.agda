module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → 0 ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_≤′_ : ℕ → ℕ → Set
0 ≤′ n = ⊤
suc m ≤′ 0 = ⊥
suc m ≤′ suc n = m ≤′ n

f : {n m : ℕ} → n ≤ m → n ≤ suc m
f z≤n = z≤n
f (s≤s x) = s≤s (f x)

f′ : {n m : ℕ} → n ≤′ m → n ≤′ suc m
f′ {zero} x = tt
f′ {suc n} {zero} ()
f′ {suc n} {suc m} x = f′ {n} {m} x

_≡_ : ℕ → ℕ → Set
0 ≡ 0 = ⊤
0 ≡ suc m = ⊥
suc m ≡ 0 = ⊥
suc m ≡ suc n = m ≡ n

_≠_ : ℕ → ℕ → Set
0 ≠ 0 = ⊥
0 ≠ suc m = ⊤
suc m ≠ 0 = ⊤
suc m ≠ suc n = m ≠ n

mutual
  Even : ℕ → Set
  Even 0 = ⊤
  Even (suc x) = Odd x
  Odd : ℕ → Set
  Odd 0 = ⊥
  Odd (suc x) = Even x

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- Maybe : Set → Set
-- Maybe A = ⊤ ⊎ A

_>_ : ℕ → ℕ → Set
n > m = m < n

_≥_ : ℕ → ℕ → Set
n ≥ m = m ≤ n

¬ : Set → Set
¬ A = A → ⊥

Fin₀ : ℕ → Set
Fin₀ 0 = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n

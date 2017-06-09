module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

≤-refl : (n : ℕ) → n ≤ n
≤-refl 0 = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n _ = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

total : ∀ m n → m ≤ n ⊎ n ≤ m
total zero n = inj₁ z≤n
total (suc m) zero = inj₂ z≤n
total (suc m) (suc n) = [ f , g ]′ (total m n) where
  f : m ≤ n → suc m ≤ suc n ⊎ suc n ≤ suc m
  f t = inj₁ (s≤s t)
  g : n ≤ m → suc m ≤ suc n ⊎ suc n ≤ suc m
  g t = inj₂ (s≤s t)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s x) = x

≤-mono : ∀ {m n k} → n ≤ m → k + n ≤ k + m
≤-mono {m} {n} {0} z≤n = z≤n
≤-mono {m} {n} {suc k} z≤n = s≤s (≤-mono {m} {n} {k} z≤n)
≤-mono {m} {n} {0} (s≤s t) = s≤s t
≤-mono {m} {n} {suc k} (s≤s t) = s≤s (≤-mono {m} {n} {k} (s≤s t))

≤-step : {m n : ℕ} → m ≤ n → m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s n) = s≤s (≤-step n)

≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b
≤′⇒≤ {a} ≤′-refl = ≤-refl a
≤′⇒≤ (≤′-step x) = ≤-step (≤′⇒≤ x)

z≤′n : ∀ n → 0 ≤′ n
z≤′n zero = ≤′-refl
z≤′n (suc m) = ≤′-step (z≤′n m)

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl = ≤′-refl
s≤′s (≤′-step x) = ≤′-step (s≤′s x)

≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b
≤⇒≤′ {b = b} z≤n = z≤′n b
≤⇒≤′ (s≤s x) = s≤′s (≤⇒≤′ x)

fin≤ : ∀ {n} (m : Fin n) → toℕ m < n
fin≤ zero = s≤s z≤n
fin≤ (suc m) = s≤s (fin≤ m)

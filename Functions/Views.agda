module Functions.Views where

open import Data.Nat using (ℕ; zero; suc; _<_; _>_; s≤s; z≤n; _+_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zero : Even zero
  odd : ∀ {n} → Odd n → Even (suc n)

data Odd where
  even : ∀ {n} → Even n → Odd (suc n)

parity : ∀ n → Even n ⊎ Odd n
parity zero = inj₁ zero
parity (suc zero) = inj₂ (even zero)
parity (suc (suc x)) with parity x
... | inj₁ p = inj₁ (odd (even p))
... | inj₂ p = inj₂ (even (odd p))

ordering : ∀ n m → n < m ⊎ n ≡ m ⊎ n > m
ordering zero zero = inj₂ (inj₁ refl)
ordering zero (suc m) = inj₁ (s≤s z≤n)
ordering (suc n) zero = inj₂ (inj₂ (s≤s z≤n))
ordering (suc n) (suc m) with ordering n m
... | inj₁ n<m = inj₁ (s≤s n<m)
... | inj₂ (inj₁ n≡m) = inj₂ (inj₁ (cong suc n≡m))
... | inj₂ (inj₂ n>m) = inj₂ (inj₂ (s≤s n>m))

data Parity : ℕ → Set where
  even : ∀ n → Parity (n * 2)
  odd : ∀ n → Parity (1 + n * 2)

data Ordering : ℕ → ℕ → Set where
  less : ∀ m k → Ordering m (suc (m + k))
  equal : ∀ m → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

parity′ : ∀ n → Parity n
parity′ zero = even 0
parity′ (suc zero) = odd 0
parity′ (suc (suc n)) with parity′ n
... | even x = even (suc x)
... | odd x = odd (suc x)

compare : ∀ m n → Ordering m n
compare zero zero = equal 0
compare zero (suc n) = less 0 n
compare (suc m) zero = greater 0 m
compare (suc m) (suc n) with compare m n
... | less k l = less (suc k) l
... | equal k = equal (suc m)
... | greater k l = greater (suc k) l

⌊_/2⌋ : ℕ → ℕ
⌊ x /2⌋ with parity′ x
... | even p = p
... | odd p = p

data Rem0 : ℕ → Set
data Rem1 : ℕ → Set
data Rem2 : ℕ → Set
data Rem3 : ℕ → Set

data Rem0 where
  zero : Rem0 0
  _+1 : ∀ {n} → Rem3 n → Rem0 (suc n)

data Rem1 where
  _+1 : ∀ {n} → Rem0 n → Rem1 (suc n)

data Rem2 where
  _+1 : ∀ {n} → Rem1 n → Rem2 (suc n)

data Rem3 where
  _+1 : ∀ {n} → Rem2 n → Rem3 (suc n)

mod4 : ∀ n → Rem0 n ⊎ Rem1 n ⊎ Rem2 n ⊎ Rem3 n
mod4 zero = inj₁ zero
mod4 (suc zero) = inj₂ (inj₁ (zero +1))
mod4 (suc (suc zero)) = inj₂ (inj₂ (inj₁ (zero +1 +1)))
mod4 (suc (suc (suc zero))) = inj₂ (inj₂ (inj₂ (zero +1 +1 +1)))
mod4 (suc (suc (suc (suc n)))) with mod4 n
... | inj₁ p = inj₁ (p +1 +1 +1 +1)
... | inj₂ (inj₁ p) = inj₂ (inj₁ (p +1 +1 +1 +1))
... | inj₂ (inj₂ (inj₁ p)) = inj₂ (inj₂ (inj₁ (p +1 +1 +1 +1)))
... | inj₂ (inj₂ (inj₂ p)) = inj₂ (inj₂ (inj₂ (p +1 +1 +1 +1)))

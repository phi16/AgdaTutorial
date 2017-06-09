module Sets.With_Functions where

open import Data.Nat
open import Data.Empty using (⊥)
open import Data.List using (List; length)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

data Even : ℕ → Set where
  double : ∀ n → Even (n + n)

data Even′ (m : ℕ) : Set where
  double : ∀ n → m ≡ n + n → Even′ m

toEven : ∀ {m} → Even′ m → Even m
toEven (double n refl) = double n
toEven′ : ∀ {m} → Even m → Even′ m
toEven′ (double n) = double n refl

suc-+ : ∀ n m → suc (n + m) ≡ n + suc m
suc-+ zero m = refl
suc-+ (suc n) m = cong suc (suc-+ n m)

prev-≡ : ∀ {n m} → suc n ≡ suc m → n ≡ m
prev-≡ refl = refl

nextEven′ : ∀ {n} → Even′ n → Even′ (suc (suc n))
nextEven′ (double n₁ refl) = double (suc n₁) (cong suc (suc-+ n₁ n₁))

prevEven′ : ∀ {n} → Even′ (suc (suc n)) → Even′ n
prevEven′ (double zero ())
prevEven′ (double (suc n) x) = double n (prev-≡ (trans (prev-≡ x) (sym (suc-+ n n))))

¬Even′1 : Even′ 1 → ⊥
¬Even′1 (double zero ())
¬Even′1 (double (suc zero) ())
¬Even′1 (double (suc (suc n)) ())

isEven′ : (n : ℕ) → Dec (Even′ n)
isEven′ zero = yes (double 0 refl)
isEven′ (suc zero) = no ¬Even′1
isEven′ (suc (suc x)) with isEven′ x
... | yes e = yes (nextEven′ e)
... | no ¬p = no (λ t → ¬p (prevEven′ t))

¬Even1 : ∀ {n} → Even n → n ≡ 1 → ⊥
¬Even1 (double zero) ()
¬Even1 (double (suc zero)) ()
¬Even1 (double (suc (suc n))) ()

nextEven : ∀ {n} → Even n → Even (suc (suc n))
nextEven (double n) with Even (suc (suc (n + n))) | cong Even (cong suc (suc-+ n n))
... | .(Even (suc n + suc n)) | refl = double (suc n)
-- nextEven (double n) rewrite cong suc (suc-+ n n) = double (suc n)
-- nextEven (double n) rewrite cong Even (cong suc (suc-+ n n)) = double (suc n)

prevEven : ∀ {n} → Even (suc (suc n)) → Even n
prevEven e = toEven (prevEven′ (toEven′ e))

isEven : (n : ℕ) → Dec (Even n)
isEven zero = yes (double 0)
isEven (suc zero) = no (λ t → ¬Even1 t refl)
isEven (suc (suc n)) with isEven n
... | yes e = yes (nextEven e)
... | no ¬p = no (λ x → ¬p (prevEven x))

data _≤‴_ : ℕ → ℕ → Set where
  diff : ∀ i j → i ≤‴ j + i

infix 4 _≤‴_

data Vec (A : Set) : ℕ → Set where
  vec : (x : List A) → Vec A (length x)

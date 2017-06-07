module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)
open import Sets.Recursive using (ℕ⁺; one; double; double+1)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixl 1 _⊎_

p₁ : ⊤ × ⊤
p₁ = tt , tt
-- p₂ : ⊤ × ⊥
-- p₃ : ⊥ × ⊥
p₄ : ⊤ ⊎ ⊤
p₄ = inj₁ tt
p₅ : ⊤ ⊎ ⊥
p₅ = inj₁ tt
-- p₆ : ⊥ ⊎ ⊥
p₇ : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
p₇ = inj₂ tt

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

1≤10 : 1 ≤ 10
1≤10 = s≤s z≤n

3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

data _isDoubleOf_ : ℕ → ℕ → Set where
  onZero : 0 isDoubleOf 0
  onSucc : {m n : ℕ} → m isDoubleOf n → (suc (suc m)) isDoubleOf (suc n)

8=2×4 : 8 isDoubleOf 4
8=2×4 = onSucc (onSucc (onSucc (onSucc onZero)))

9≠2×4 : 9 isDoubleOf 4 → ⊥
9≠2×4 (onSucc (onSucc (onSucc (onSucc ()))))

data Odd′ : ℕ → Set where
  one : Odd′ 1
  ssuc : {m : ℕ} → Odd′ m → Odd′ (suc (suc m))

odd9 : Odd′ 9
odd9 = ssuc (ssuc (ssuc (ssuc one)))

¬odd8 : Odd′ 8 → ⊥
¬odd8 (ssuc (ssuc (ssuc (ssuc ()))))

data Even : ℕ → Set
data Odd : ℕ → Set

data Even where
  zero : Even 0
  succ : {m : ℕ} → Odd m → Even (suc m)
data Odd where
  succ : {m : ℕ} → Even m → Odd (suc m)

data _≡_ : ℕ → ℕ → Set where
  zero : 0 ≡ 0
  succ : {m : ℕ} → m ≡ m → suc m ≡ suc m

data _≠_ : ℕ → ℕ → Set where
  zero : {m : ℕ} → 0 ≠ suc m
  succ : {m n : ℕ} → m ≠ n → suc m ≠ suc n

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} → m ≤′ m
  ≤′-step : {m n : ℕ} → m ≤′ n → m ≤′ suc n

infix 4 _≤′_

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → 0 + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

5+5≡10 : 5 + 5 ≡ 10
5+5≡10 = sns (sns (sns (sns (sns znn))))
2+2≠5 : 2 + 2 ≡ 5 → ⊥
2+2≠5 (sns (sns ()))

data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  zero : ∀ {m} → 0 ⊓ m ≡ 0
  succ : ∀ {m n k} → m ⊓ n ≡ k → suc m ⊓ suc n ≡ suc k

3⊓5≡3 : 3 ⊓ 5 ≡ 3
3⊓5≡3 = succ (succ (succ zero))
3⊓5≠5 : 3 ⊓ 5 ≡ 5 → ⊥
3⊓5≠5 (succ (succ (succ ())))

data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  zero : ∀ {m} → 0 ⊔ m ≡ m
  succ : ∀ {m n k} → m ⊔ n ≡ k → suc m ⊔ suc n ≡ suc k

3⊓5≡5 : 3 ⊔ 5 ≡ 5
3⊓5≡5 = succ (succ (succ zero))
3⊓5≠3 : 3 ⊔ 5 ≡ 3 → ⊥
3⊓5≠3 (succ (succ (succ ())))

data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

data _isDoubleOf′_ : ℕ → ℕ → Set where
  witness : ∀ {m n} → n + n ≡ m → m isDoubleOf′ n

8=2×4′ : 8 isDoubleOf′ 4
8=2×4′ = witness (sns (sns (sns (sns znn))))
9≠2×4′ : 9 isDoubleOf′ 4 → ⊥
9≠2×4′ (witness (sns (sns (sns (sns ())))))

data _*_≡_ : ℕ → ℕ → ℕ → Set where
  zero : ∀ {n} → 0 * n ≡ 0
  succ : ∀ {m n k l} → m * n ≡ k → n + k ≡ l → suc m * n ≡ l

3*3≡9 : 3 * 3 ≡ 9
3*3≡9 = succ (succ (succ zero (sns (sns (sns znn)))) (sns (sns (sns znn)))) (sns (sns (sns znn)))
3*3≠8 : 3 * 3 ≡ 8 → ⊥
3*3≠8 (succ (succ (succ zero (sns (sns (sns znn)))) (sns (sns (sns znn)))) (sns (sns (sns ()))))

data _≈_ : ℕ → ℕ⁺ → Set where
  ≈-one : 1 ≈ one
  ≈-double : {m n : ℕ} {k : ℕ⁺} → m ≈ k → n isDoubleOf m → n ≈ double k
  ≈-double+1 : {m n : ℕ} {k : ℕ⁺} → m ≈ k → n isDoubleOf m → suc n ≈ double+1 k

5≈d¹d1 : 5 ≈ double+1 (double one)
5≈d¹d1 = ≈-double+1 (≈-double ≈-one (onSucc onZero)) (onSucc (onSucc onZero))
4≉d¹d1 : 4 ≈ double+1 (double one) → ⊥
4≉d¹d1 (≈-double+1 x (onSucc ()))

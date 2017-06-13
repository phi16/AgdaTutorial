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

syntax ex (λ y → x) = ∃ y , x

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
  infixr 3 _↪_ -- hookrightarrow
  infixr 5 _∷_

  data Into (n : ℕ) : Set where
    _↪_ : A → V n → Into n

  data _≋_ : ∀ {n} → Into n → V (suc n) → Set where
    zero : ∀ {n x} {xs : V n} → x ↪ xs ≋ x ∷ xs
    suc : ∀ {n x y} {xs : V n} {ys} → x ↪ xs ≋ ys → x ↪ y ∷ xs ≋ y ∷ ys

  data _≈_ : ∀ {n} → V n → V n → Set where
    [] : [] ≈ []
    _∷_ : ∀ {n x} {xs ys : V n} {xxs} → x ↪ xs ≋ xxs → ys ≈ xs → x ∷ ys ≈ xxs

  ≈-refl : ∀ {n} {xs : V n} → xs ≈ xs
  ≈-refl {xs = []} = []
  ≈-refl {xs = x ∷ xs} = zero ∷ ≈-refl

  ~↪ : ∀ {n x} {xs : V n} {ys} → x ↪ xs ≋ ys → x ∷ xs ~ ys
  ~↪ zero = ~-refl
  ~↪ (suc x₁) = exch ∘simp sucSimp (~↪ x₁)

  ≈→~ : ∀ {n} {xs ys : V n} → xs ≈ ys → xs ~ ys
  ≈→~ [] = zero
  ≈→~ (x₁ ∷ x₂) = sucSimp (≈→~ x₂) ∘simp ~↪ x₁

  ↪-exch : ∀ {n x y} {xs : V n} {xxs yxxs} → x ↪ xs ≋ xxs → y ↪ xxs ≋ yxxs → ∃ yxs , (y ↪ xs ≋ yxs) × (x ↪ yxs ≋ yxxs)
  ↪-exch zero zero = _ , zero , suc zero
  ↪-exch zero (suc q) = _ , q , zero
  ↪-exch (suc p) zero = _ , zero , suc (suc p)
  ↪-exch (suc p) (suc q) with ↪-exch p q
  ... | _ , s , t = _ , suc s , suc t

  getOut : ∀ {n x} {xs : V n} {xxs xys} → x ↪ xs ≋ xxs → xxs ≈ xys → ∃ ys , (x ↪ ys ≋ xys) × (xs ≈ ys)
  getOut zero (x₁ ∷ q) = _ , x₁ , q
  getOut (suc p) (x₁ ∷ q) with getOut p q
  ... | _ , m , f with ↪-exch m x₁
  ... | _ , k , r = _ , r , k ∷ f

  infixl 3 _∘≈_

  _∘≈_ : ∀ {n} {xs ys zs : V n} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  [] ∘≈ q = q
  x₁ ∷ p ∘≈ q with getOut x₁ q
  ... | _ , b , c = b ∷ (p ∘≈ c)

  ~→≈ : ∀ {n} {xs ys : V n} → xs ~ ys → xs ≈ ys
  ~→≈ zero = []
  ~→≈ (suc x) = zero ∷ ~→≈ x
  ~→≈ (x ∘ x₁) = ~→≈ x ∘≈ ~→≈ x₁
  ~→≈ exch = suc zero ∷ ≈-refl

  ≈-sym : ∀ {n} {xs ys : V n} → xs ≈ ys → ys ≈ xs
  ≈-sym a = ~→≈ (~-sym (≈→~ a))

  cancel : ∀ {n} {x} {xs ys : V n} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
  cancel (zero ∷ x₂) = x₂
  cancel (suc x₂ ∷ x₃ ∷ x₄) = zero ∷ x₄ ∘≈ x₃ ∷ ≈-refl ∘≈ x₂ ∷ ≈-refl

t1 : 1 ∷ 2 ∷ 3 ∷ 4 ∷ [] ≈ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []
t1 = suc (suc (suc zero)) ∷ suc zero ∷ ≈-refl

f2 : 1 ∷ 2 ∷ [] ≈ 1 ∷ 1 ∷ [] → ⊥
f2 (zero ∷ () ∷ x)
f2 (suc zero ∷ () ∷ x₁)

module _ {A : Set} {{eq : Decidable {A = A} _≡_}} where

  private V = Vec A

  getOut′ : ∀ {n} x (xs : V (suc n)) → Dec (∃ ys , x ↪ ys ≋ xs)
  getOut′ = {!   !}

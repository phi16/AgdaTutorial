module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

refl' : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity 0 = refl
+-right-identity (suc n) = cong suc (+-right-identity n)

+-left-identity : ∀ a → 0 + a ≡ a
+-left-identity _ = refl

+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero = +-right-identity m
+-comm m (suc n) = trans (m+1+n≡1+m+n m n) (cong suc (+-comm m n))

fromList : List ⊤ → ℕ
fromList [] = 0
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList 0 = []
toList (suc n) = tt ∷ toList n

from-to : ∀ a → fromList (toList a) ≡ a
from-to zero = refl
from-to (suc x) = cong suc (from-to x)

to-from : ∀ a → toList (fromList a) ≡ a
to-from [] = refl
to-from (x ∷ x₁) = cong (_∷_ x) (to-from x₁)

fromPreserves++ : ∀ (a b : List ⊤) → fromList (a ++ b) ≡ fromList a + fromList b
fromPreserves++ [] b = refl
fromPreserves++ (x ∷ a) b = cong suc (fromPreserves++ a b)

toPreserves+ : ∀ (a b : ℕ) → toList (a + b) ≡ toList a ++ toList b
toPreserves+ 0 y = refl
toPreserves+ (suc x) y = cong (_∷_ tt) (toPreserves+ x y)

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix 3 _∎

+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ 0 n = sym (+-right-identity n)
+-comm′ (suc m) n =
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm′ m n) ⟩
    suc (n + m)
  ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
    n + suc m
  ∎

distribᵣ-*-+ : ∀ a b c → (a + b) * c ≡ a * c + b * c
distribᵣ-*-+ zero b c = refl
distribᵣ-*-+ (suc a) b c =
    (suc a + b) * c
  ≡⟨ refl ⟩
    c + (a + b) * c
  ≡⟨ cong (_+_ c) (distribᵣ-*-+ a b c) ⟩
    c + (a * c + b * c)
  ≡⟨ +-assoc c (a * c) (b * c) ⟩
    (c + a * c) + b * c
  ≡⟨ refl ⟩ -- cong (λ t → t + b * c) ?
    suc a * c + b * c
  ∎

*-assoc : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc zero b c = refl
*-assoc (suc a) b c =
    suc a * (b * c)
  ≡⟨ refl ⟩
    b * c + a * (b * c)
  ≡⟨ cong (_+_ (b * c)) (*-assoc a b c) ⟩
    b * c + (a * b) * c
  ≡⟨ sym (distribᵣ-*-+ b (a * b) c) ⟩
    (b + a * b) * c
  ≡⟨ refl ⟩
    suc a * b * c
  ∎

*-left-identity : ∀ a → 1 * a ≡ a
*-left-identity zero = refl
*-left-identity (suc x) =
    1 * suc x
  ≡⟨ refl ⟩
    suc x + 0 * suc x
  ≡⟨ cong (_+_ (suc x)) refl ⟩
    suc x + 0
  ≡⟨ +-right-identity (suc x) ⟩
    suc x
  ∎

*-right-identity : ∀ a → a * 1 ≡ a
*-right-identity zero = refl
*-right-identity (suc x) =
    suc x * 1
  ≡⟨ refl ⟩
    1 + x * 1
  ≡⟨ cong (_+_ 1) (*-right-identity x) ⟩
    1 + x
  ≡⟨ refl ⟩
    suc x
  ∎

n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) =
    suc n * 0
  ≡⟨ refl ⟩
    0 + n * 0
--  ≡⟨ cong (_+_ 0) (n*0≡0 n) 〉 -- NG
--  ≡⟨ cong (_+_ 0) (n*0≡0 n) ⟩ -- OK
  ≡⟨ cong (_+_ 0) (n*0≡0 n) ⟩
    0 + 0
  ≡⟨ refl ⟩
    0
  ∎

*-suc : ∀ n m → n + n * m ≡ n * suc m
*-suc zero m = refl
*-suc (suc n) m =
    suc n + suc n * m
  ≡⟨ refl ⟩
    suc (n + suc n * m)
  ≡⟨ refl ⟩
    suc (n + (m + n * m))
  ≡⟨ cong suc (+-assoc n m (n * m)) ⟩
    suc ((n + m) + n * m)
  ≡⟨ cong (λ t → suc (t + n * m)) (+-comm′ n m) ⟩
    suc (m + n + n * m)
  ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
    suc (m + (n + n * m))
  ≡⟨ cong (λ t → suc (m + t)) (*-suc n m) ⟩
    suc (m + n * suc m)
  ≡⟨ refl ⟩
    suc m + n * suc m
  ≡⟨ refl ⟩
    suc n * suc m
  ∎

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero n = sym (n*0≡0 n)
*-comm (suc m) n =
    suc m * n
  ≡⟨ refl ⟩
    n + m * n
  ≡⟨ cong (_+_ n) (*-comm m n) ⟩
    n + n * m
  ≡⟨ *-suc n m ⟩
    n * suc m
  ∎

module trySemiringSolver where
  open import Data.Nat
  open import Data.Nat.Properties
  open SemiringSolver
  open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡-official_)

  f : ∀ a b c → a + b * c + 1 ≡-official 1 + c * b + a
  f = solve 3 (λ a b c → a :+ b :* c :+ con 1 := con 1 :+ c :* b :+ a) refl

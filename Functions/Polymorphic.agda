module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Sets.Parametric using (_×_; _,_; _⊎_; inj₁; inj₂)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

infixr 5 _++_

fromList : List ⊤ → ℕ
fromList [] = 0
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc x) = tt ∷ toList x

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

safeHead : {A : Set} → List A → Maybe A
safeHead [] = Nothing
safeHead (x ∷ _) = Just x

safeTail : {A : Set} → List A → Maybe (List A)
safeTail [] = Nothing
safeTail (_ ∷ xs) = Just xs

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

maps : {A B : Set} → List (A → B) → List A → List B
maps [] _ = []
maps (f ∷ fs) [] = []
maps (f ∷ fs) (y ∷ ys) = f y ∷ maps fs ys

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

id : {A : Set} → A → A
id a = a

aNumber : ℕ
aNumber = id {ℕ} (suc zero)

const : {A B : Set} → A → B → A
const x y = x

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f y x = f x y

×-swap : {A B : Set} → A × B → B × A
×-swap (x₁ , x₂) = x₂ , x₁

proj₁ : {A B : Set} → A × B → A
proj₁ (x₁ , _) = x₁

⊎-swap : {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap (inj₁ x) = inj₂ x
⊎-swap (inj₂ x) = inj₁ x

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ x) = g x

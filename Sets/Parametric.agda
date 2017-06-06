module Sets.Parametric where

open import Sets.Enumerated using (Bool; false; true; ⊤; tt)
open import Data.Nat

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

data BinTree (A : Set) : Set where
  leaf : A → BinTree A
  node : BinTree A → BinTree A → BinTree A

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixl 1 _⊎_

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  [] : List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B

e₁ e₂ e₃ e₄ e₅ : List₁ ⊤ Bool
e₁ = []
e₂ = tt ∷ true ∷ []
e₃ = tt ∷ false ∷ []
e₄ = tt ∷ true ∷ tt ∷ true ∷ []
e₅ = tt ∷ true ∷ tt ∷ false ∷ []

data AlterList (A B : Set) : Set where
  [] : AlterList A B
  _∷_ : A → AlterList B A → AlterList A B

a₁ a₂ a₃ a₄ : AlterList ⊤ Bool
a₁ = []
a₂ = tt ∷ true ∷ []
a₃ = tt ∷ false ∷ []
a₄ = tt ∷ true ∷ tt ∷ true ∷ []

r₁ r₂ r₃ r₄ : AlterList Bool ⊤
r₁ = []
r₂ = true ∷ tt ∷ []
r₃ = false ∷ tt ∷ []
r₄ = true ∷ tt ∷ true ∷ tt ∷ []

data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero : A → Square A
  suc : Square (T4 A) → Square A

t₁ : Square ℕ
t₁ = zero 5
t₂ : Square ℕ
t₂ = suc (zero (quad 1 2 3 4))
t₃ : Square ℕ
t₃ = suc (suc (zero (quad (quad 1 2 3 4) (quad 5 6 7 8) (quad 9 10 11 12) (quad 13 14 15 16))))

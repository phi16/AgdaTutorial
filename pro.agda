module pro where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
import Relation.Binary.EqReasoning as EqR

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

record IsSemigroup {A : Set} (_∙_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

ℕ+-isSemigroup : IsSemigroup _+_
ℕ+-isSemigroup = ?

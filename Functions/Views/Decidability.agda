module Functions.Views.Decidability where

open import Data.Nat   using (ℕ; zero; suc; pred; _+_; _≤_; s≤s; z≤n; _<_; _>_)
open import Data.Bool  using (Bool; true; false; if_then_else_; not)
open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)
open import Function   using (const; _$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

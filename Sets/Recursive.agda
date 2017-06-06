module Sets.Recursive where

open import Sets.Enumerated using (Bool; true; false)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data ℕ⁺ : Set where
  one : ℕ⁺
  double : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id : ℕ⁺ → ℕ₂

nine : ℕ₂
nine = id (double+1 (double (double one)))

data ℤ : Set where
  negative : ℕ⁺ → ℤ
  zero : ℤ
  positive : ℕ⁺ → ℤ

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

tree1 : BinTree
tree1 = leaf

tree2 : BinTree
tree2 = node leaf leaf

tree3 : BinTree
tree3 = node tree2 tree2

tree4 : BinTree
tree4 = node (node tree2 leaf) leaf

data leafℕ-BinTree : Set where
  leaf : ℕ → leafℕ-BinTree
  node : leafℕ-BinTree → leafℕ-BinTree → leafℕ-BinTree

data nodeℕ-BinTree : Set where
  leaf : nodeℕ-BinTree
  node : nodeℕ-BinTree → ℕ → nodeℕ-BinTree → nodeℕ-BinTree

data nBlℕ-BinTree : Set where
  leaf : ℕ → nBlℕ-BinTree
  node : nBlℕ-BinTree → Bool → nBlℕ-BinTree → nBlℕ-BinTree

data ℕ-List : Set where
  nil : ℕ-List
  cons : ℕ → ℕ-List → ℕ-List

data ℕ-NonEmpty : Set where
  last : ℕ → ℕ-NonEmpty
  cons : ℕ → ℕ-NonEmpty → ℕ-NonEmpty

module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M

l : L
l = 5 ∷ (false ∷ nil)

m : M
m = true ∷ (2 ∷ (false ∷ nil))

data Rose : Set
data Tree : Set

data Rose where
  nil : Rose
  cons : Tree → Rose → Rose

data Tree where
  children : Rose → Tree

tree : Tree
tree = children (cons (children nil) (cons (children nil) nil))

data Expr : Set
data Term : Set
data Factor : Set

data Expr where
  e : Term → Expr
  _+_ : Expr → Term → Expr
  _-_ : Expr → Term → Expr

data Term where
  e : Factor → Term
  _×_ : Term → Factor → Term
  _÷_ : Term → Factor → Term

data Factor where
  nat : ℕ → Factor
  paren : Expr → Factor

exExpr : Expr
exExpr = e (e (nat 3) × nat 7) + e (nat 5)

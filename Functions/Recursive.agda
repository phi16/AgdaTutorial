module Functions.Recursive where

open import Data.Bool using (Bool; true; false; not)
open import Data.Nat using (ℕ; suc; zero)
open import Sets.Recursive using (BinTree; leaf; node)

_+_ : ℕ → ℕ → ℕ
0 + n = n
suc m + n = suc (m + n)

infixl 6 _+_

pred : ℕ → ℕ
pred 0 = 0
pred (suc m) = m

_-_ : ℕ → ℕ → ℕ
0 - n = 0
suc m - 0 = suc m
suc m - suc n = m - n

infixl 6 _-_

_*_ : ℕ → ℕ → ℕ
0 * n = 0
suc m * n = n + m * n

infixl 7 _*_

_⊔_ : ℕ → ℕ → ℕ
0 ⊔ y = y
suc x ⊔ 0 = suc x
suc x ⊔ suc y = suc (x ⊔ y)

infixl 6 _⊔_

_⊓_ : ℕ → ℕ → ℕ
0 ⊓ y = 0
suc x ⊓ 0 = 0
suc x ⊓ suc y = suc (x ⊓ y)

infixl 7 _⊓_

⌊_/2⌋ : ℕ → ℕ
⌊ 0 /2⌋ = 0
⌊ 1 /2⌋ = 0
⌊ suc (suc x) /2⌋ = suc ⌊ x /2⌋

odd : ℕ → Bool
odd 0 = false
odd (suc x) = not (odd x)

even : ℕ → Bool
even 0 = true
even (suc x) = not (even x)

mutual
  even′ : ℕ → Bool
  even′ 0 = true
  even′ (suc x) = odd′ x

  odd′ : ℕ → Bool
  odd′ 0 = false
  odd′ (suc x) = even′ x

_≡?_ : ℕ → ℕ → Bool
0 ≡? 0 = true
0 ≡? suc y = false
suc x ≡? 0 = false
suc x ≡? suc y = x ≡? y

_≤?_ : ℕ → ℕ → Bool
0 ≤? 0 = true
0 ≤? suc y = true
suc x ≤? 0 = false
suc x ≤? suc y = x ≤? y

open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

from : ℕ₂ → ℕ
from zero = 0
from (id one) = 1
from (id (double x)) = 2 * from (id x)
from (id (double+1 x)) = suc (2 * from (id x))

data ℤ : Set where
  Z : ℤ
  _⁺¹ : ℕ → ℤ
  -_⁻¹ : ℕ → ℤ

sub : ℕ → ℕ → Bool → Bool → ℤ
sub x y true _ = Z
sub x y false false = (x - y - 1)⁺¹
sub x y false true = -(y - x - 1)⁻¹

_+′_ : ℤ → ℤ → ℤ
Z +′ y = y
(x ⁺¹) +′ Z = x ⁺¹
(x ⁺¹) +′ (x₁ ⁺¹) = (x + x₁ + 1) ⁺¹
(x ⁺¹) +′ - x₁ ⁻¹ = sub x x₁ (x ≡? x₁) (x ≤? x₁)
- x ⁻¹ +′ Z = - x ⁻¹
- x ⁻¹ +′ (x₁ ⁺¹) = sub x₁ x (x₁ ≡? x) (x₁ ≤? x)
- x ⁻¹ +′ - x₁ ⁻¹ = - (x + x₁ + 1) ⁻¹

infixl 6 _+′_

mul : ℕ → ℤ → ℤ
mul zero y = Z
mul (suc x) y = y +′ mul x y

neg : ℤ → ℤ
neg Z = Z
neg (x ⁺¹) = - x ⁻¹
neg (- x ⁻¹) = x ⁺¹

_-′_ : ℤ → ℤ → ℤ
x -′ y = x +′ neg y

_*′_ : ℤ → ℤ → ℤ
Z *′ y = Z
(x ⁺¹) *′ y = mul x y +′ y
- x ⁻¹ *′ y = neg (mul x y +′ y)

mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node x y) = node (mirror y) (mirror x)

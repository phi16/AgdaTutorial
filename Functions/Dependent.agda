module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ 0 = zero
fromℕ (suc n) = suc (fromℕ n)

_-_ : (n : ℕ) → Fin (suc n) → ℕ
m - zero = m
zero - suc ()
suc m - suc n = m - n

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc n) = suc (toℕ n)

fromℕ≤ : ∀ {m n} → m < n → Fin n
fromℕ≤ {zero} (s≤s z≤n) = zero
fromℕ≤ {suc m} (s≤s x) = suc (fromℕ≤ {m} x)

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ x zero = zero
inject+ x (suc y) = suc (inject+ x y)

four : Fin 66
four = suc (suc (suc (suc zero)))

raise : ∀ {m} n → Fin m → Fin (n + m)
raise zero y = y
raise (suc x) y = suc (raise x y)

head : ∀ {n} {A : Set} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {n} {A : Set} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

_++_ : ∀ {n m} {A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

maps : ∀ {n} {A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (x ∷ xs) = f x ∷ maps fs xs

replicate : ∀ {n} {A : Set} → A → Vec A n
replicate {zero} x = []
replicate {suc n} x = x ∷ replicate {n} x

map : ∀ {n} {A B : Set} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

zip : ∀ {n} {A B : Set} → Vec A n → Vec B n → Vec (A × B) n
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

_!_ : ∀ {n} {A : Set} → Vec A n → Fin n → A
(x ∷ xs) ! zero = x
(x ∷ xs) ! suc n = xs ! n

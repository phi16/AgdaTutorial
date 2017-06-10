module Sets.Records where

open import Data.Nat
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq

record R : Set where
  field
    r₁ : Bool
    r₂ : ℕ

x : R
x = record { r₁ = true; r₂ = 2 }

r : Bool → ℕ → R
r b n = record { r₁ = b; r₂ = n }

x′ = r true 2

record R′ : Set where
  constructor r′
  field
    r₁ : Bool
    r₂ : ℕ

x″ = r′ true 2

sel₁ : R → Bool
sel₁ = R.r₁

sel₂ : R → ℕ
sel₂ = R.r₂

x‴ = r (R.r₁ x) (R.r₂ x)

data R″ : Set where
  r″ : (r₁ : Bool) (r₂ : ℕ) → R″

r₁ : R″ → Bool
r₁ (r″ a b) = a

r₂ : R″ → ℕ
r₂ (r″ a b) = b

extRec : (x : R) → x ≡ r (R.r₁ x) (R.r₂ x)
extRec x = Eq.refl

extData : (x : R″) → x ≡ r″ (r₁ x) (r₂ x)
extData (r″ r₁ r₂) = Eq.refl

-- record equality seems to be regared as "pointwise"

record ⊤ : Set where

record _×_ (A B : Set) : Set where
  field
    π₁ : A
    π₂ : B

open import Data.Vec using (Vec; []; _∷_)

record Listℕ : Set where
  constructor Lℕ
  field
    length : ℕ
    vector : Vec ℕ length

list : Listℕ
list = Lℕ 3 (0 ∷ 1 ∷ 2 ∷ [])

list′ : Listℕ
list′ = Lℕ _ (0 ∷ 1 ∷ 2 ∷ [])

length′ : Listℕ → ℕ
length′ = Listℕ.length

vector′ : (x : Listℕ) → Vec ℕ (length′ x)
vector′ = Listℕ.vector

record List (A : Set) : Set where
  constructor L
  field
    length : ℕ
    vector : Vec A length

list₂ : List Bool
list₂ = L _ (true ∷ false ∷ true ∷ [])

length″ : {A : Set} → List A → ℕ
length″ = List.length

vector″ : {A : Set} (x : List A) → Vec A (length″ x)
vector″ = List.vector

record Σ (A : Set) (P : A → Set) : Set where
  constructor exist
  field
    witness : A
    proof : P witness

record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl : {x : A} → x ≈ x
    sym : {x y : A} → x ≈ y → y ≈ x
    trans : {x y z : A} → x ≈ y → y ≈ z → x ≈ z

isEquivalence : {A : Set} → IsEquivalence {A} _≡_
isEquivalence = record { refl = Eq.refl; sym = Eq.sym; trans = Eq.trans }

record IsSemigroup {A : Set} (_*_ : A → A → A) : Set where
  field
    assoc : (x y z : A) → (x * y) * z ≡ x * (y * z)

+-semigroup : IsSemigroup {ℕ} _+_
+-semigroup = record { assoc = assoc } where
  assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  assoc (zero) y z = Eq.refl
  assoc (suc x) y z = Eq.cong suc (assoc x y z)

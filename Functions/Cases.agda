module Functions.Cases where

open import Sets.Enumerated

not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ x = x
false ∧ _ = false

infixr 6 _∧_

_∨_ : Bool → Bool → Bool
false ∨ x = x
true ∨ _ = true

infixr 5 _∨_

_∨′_ : Bool → Bool → Bool
x ∨′ y = not (not x ∧ not y)

_∧ₐ_ : Answer → Answer → Answer
yes ∧ₐ x = x
no ∧ₐ _ = no
maybe ∧ₐ yes = maybe
maybe ∧ₐ maybe = maybe
maybe ∧ₐ no = no

_∨ₐ_ : Answer → Answer → Answer
no ∨ₐ x = x
yes ∨ₐ _ = yes
maybe ∨ₐ no = maybe
maybe ∨ₐ maybe = maybe
maybe ∨ₐ yes = yes

turnLeft : Quarter → Quarter
turnLeft east = north
turnLeft west = south
turnLeft north = west
turnLeft south = east

turnBack : Quarter → Quarter
turnBack x = turnLeft (turnLeft x)

turnRight : Quarter → Quarter
turnRight x = turnLeft (turnBack x)

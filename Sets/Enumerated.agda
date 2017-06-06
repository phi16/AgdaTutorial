module Sets.Enumerated where

data Bool : Set where
  true : Bool
  false : Bool

data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

data Bool' : Set where
  true' : Bool'
  false' : Bool'

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

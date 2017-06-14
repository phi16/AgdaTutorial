module Revise.InfIO where

open import Coinduction
open import Data.Unit
open import Data.String
open import Data.Colist
open import Function
import IO.Primitive as Prim
open import Level

infixl 1 _>>=_ _>>_

data IO {a} (A : Set a) : Set (suc a) where
  lift : (m : Prim.IO A) → IO A
  return : (x : A) → IO A
  _>>=_ : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  _>>_ : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

abstract
  {-# NON_TERMINATING #-}

  run : ∀ {a} {A : Set a} → IO A → Prim.IO A
  run (lift m) = m
  run (return x) = Prim.return x
  run (m >>= f) = Prim._>>=_ (run (♭ m)) λ x → run (♭ (f x))
  run (m₁ >> m₂) = Prim._>>=_ (run (♭ m₁)) λ _ → run (♭ m₂)

sequence : ∀ {a} {A : Set a} → Colist (IO A) → IO (Colist A)
sequence [] = return []
sequence (c ∷ cs) =
  ♯ c >>= λ x →
  ♯ (♯ sequence (♭ cs) >>= λ xs →
  ♯ return (x ∷ ♯ xs))

sequence′ : ∀ {a} {A : Set a} → Colist (IO A) → IO (Lift ⊤)
sequence′ [] = return _
sequence′ (c ∷ cs) =
  ♯ c >>
  ♯ (♯ sequence′ (♭ cs) >>
  ♯ return _)

mapM : ∀ {a b} {A : Set a} {B : Set b} → (A → IO B) → Colist A → IO (Colist B)
mapM f = sequence ∘ map f

mapM′ : {A B : Set} → (A → IO B) → Colist A → IO (Lift ⊤)
mapM′ f = sequence′ ∘ map f

getContents : IO Costring
getContents = lift Prim.getContents

readFile : String → IO Costring
readFile f = lift (Prim.readFile f)

readFiniteFile : String → IO String
readFiniteFile f = lift (Prim.readFiniteFile f)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s =
  ♯ lift (Prim.writeFile f s) >>
  ♯ return _

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO ⊤
appendFile∞ f s =
  ♯ lift (Prim.appendFile f s) >>
  ♯ return _

appendFile : String → String → IO ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s =
  ♯ lift (Prim.putStr s) >>
  ♯ return _

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s =
  ♯ lift (Prim.putStrLn s) >>
  ♯ return _

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)

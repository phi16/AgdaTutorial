module Revise.IO where

open import Data.Char using (Char)

char[a] : Char
char[a] = 'a'

open import Data.String using (String; Costring; toCostring; _++_)

string[hello] : String
string[hello] = "hello"

open import Data.List using (List; _∷_; [])

unlines : List String → String
unlines [] = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

open import IO.Primitive

open import Foreign.Haskell using (Unit; unit)

main : IO Unit
main = putStrLn (toCostring "Hello World!")

main′ : IO Unit
main′ = return unit

postulate getLine : IO Costring

{-# COMPILED getLine getLine #-}

main″ = getLine >>= putStrLn

open import Data.Colist renaming (_++_ to _+++_)

main‴ =
  getLine >>= λ x →
  putStrLn (toCostring "Hello " +++ x)

open import Data.Bool using (Bool; true; false; if_then_else_)

echo : IO Unit
echo =
  getLine >>= λ
  { [] → return unit
  ; xs → putStrLn xs
  }

open import Data.List renaming (_++_ to _++L_)
open import Coinduction

f : List Char → List Char → Costring → Costring
f acc [] [] = []
f acc [] ('\n' ∷ xs) = '\n' ∷ ♯ (f [] (reverse acc ++L '\n' ∷ []) (♭ xs))
f acc [] (x ∷ xs) = x ∷ ♯ f (x ∷ acc) [] (♭ xs)
f acc (x ∷ xs) zs = x ∷ ♯ f acc xs zs

trans : Costring → Costring
trans = f [] []

main⁗ = getContents >>= λ x → putStr (trans x)

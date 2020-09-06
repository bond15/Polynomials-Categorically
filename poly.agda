module poly where
open import Data.List.Base
open import Data.Product
open import Data.Nat
open import Data.Bool
open import Agda.Builtin.Nat renaming (_<_ to _l_)
-- polynomial as a list(stream?) of coefficients
data polynomial (X : Set) : Set where
  coef : List (( ℕ × X )) -> polynomial X



compareIndex : {X : Set} -> (ℕ × X) -> (ℕ × X) -> Bool
compareIndex (n₁ , x) (n₂ , y) = n₁ l n₂

insertBy : {X : Set} -> (ℕ × X) -> List (ℕ × X) -> List (ℕ × X)
insertBy p [] = p ∷ []
insertBy p (y ∷ xs) with (compareIndex p y)
...                    | true = p ∷ y ∷ xs
...                    | false = y ∷ insertBy p xs

sort : {X : Set} -> List (ℕ × X) -> List (ℕ × X)
sort xs = foldr insertBy [] xs

normalize : {X : Set} -> polynomial X -> polynomial X
normalize (coef xs) = coef (sort xs)

module poly where
open import Data.List.Base using (List ; _∷_ ; [] ; foldr ; foldl ; map ; _++_ ; inits ; length ; replicate ; zipWith)
open import Data.Product using (_×_ ; _,_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat renaming (_<_ to _l_ ; _+_ to _+ℕ_ ; _*_ to _*ℕ_)

-- polynomial as a list(stream?) of coefficients

data ℕ[X] : Set where
  coef : List ℕ -> ℕ[X]

out : ℕ[X] -> List ℕ
out (coef xs) = xs

_::_ : ℕ -> ℕ[X] -> ℕ[X]
x :: (coef p) = coef (x ∷ p)

-- poly add
_+_ : ℕ[X] -> ℕ[X] -> ℕ[X]
(coef []) + p₂ = p₂
p₁ + (coef []) = p₁
(coef (c₁ ∷ p₁)) + (coef (c₂ ∷ p₂)) = (c₁ +ℕ c₂) :: ((coef p₁) + (coef p₂))

-- scalar poly mult
_⋆_ : ℕ -> ℕ[X] -> ℕ[X]
n ⋆ (coef []) = coef []
n ⋆ (coef (x ∷ xs)) = (n *ℕ x) :: (n ⋆ (coef xs))

-- poly poly mult
_*_ : ℕ[X] -> ℕ[X] -> ℕ[X]
(coef xs) * (coef ys) = let result = map (λ (x : ℕ) -> out ( x ⋆ (coef ys))) xs
                            zeroPad = inits (replicate (length result) 0)
                            shifted = map coef (zipWith _++_ zeroPad result)
                        in foldl _+_ (coef []) shifted

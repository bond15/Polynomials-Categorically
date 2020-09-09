module poly where
open import Data.List.Base using (List ; _∷_ ; [] ; foldr ; foldl ; map ; _++_ ; inits ; length ; replicate ; zipWith)
open import Data.Product using (_×_ ; _,_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat renaming (_<_ to _l_ ; _+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong)

record monoid (A : Set) (_∙_ : A -> A -> A)(e : A) : Set where
  field
    assoc : ∀ (a b c : A) -> (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
    l-unit : ∀ (a : A) -> e ∙ a ≡ a
    r-unit : ∀ (a : A) -> a ∙ e ≡ a

record commutative-monoid (A : Set)(_∙_ : A -> A -> A)(e : A)  : Set where
  -- dependency
  field
    m : monoid A _∙_ e
  -- record type also define modules which can be opened
  -- to bring definitions into scope
  -- Not needed, only brings laws into scope
  open monoid m
  field
    commutative : ∀ (a b : A) -> a ∙ b ≡ b ∙ a

record semiring (A : Set)(_+_ : A -> A -> A)(_x_ : A -> A -> A)(e₊ : A)(eₓ : A) : Set where
  field
    +-comm-monoid : commutative-monoid A _+_ e₊
    x-monoid : monoid A _x_ eₓ
    l-distₓ : ∀ (a b c : A) -> a x (b + c) ≡ (a x b) + (a + c)
    r-distₓ : ∀ (a b c : A) -> (a + b) x c ≡ (a x c) + (b x c)
    l-e₊-annihilateₓ : ∀ (a : A) -> e₊ x a ≡ e₊
    r-e₊-annihilateₓ : ∀ (a : A) -> a x e₊ ≡ e₊

+ℕ-assoc : ∀ (a b c : ℕ) -> (a +ℕ b) +ℕ c ≡ a +ℕ (b +ℕ c)
+ℕ-assoc zero n p = refl
+ℕ-assoc (suc m) n p = cong suc (+ℕ-assoc m n p)

+ℕ-zlemma : ∀ (n : ℕ) -> n +ℕ 0 ≡ n
+ℕ-zlemma zero = refl
+ℕ-zlemma (suc m) = cong suc (+ℕ-zlemma m)

ℕ₊-monoid : monoid ℕ _+ℕ_ 0
ℕ₊-monoid = record
  { assoc = +ℕ-assoc
  ; l-unit = λ (a : ℕ) -> refl
  ; r-unit = +ℕ-zlemma
  }

+ℕ-succ : ∀ (m n : ℕ) -> m +ℕ (suc n) ≡ suc (m +ℕ n)
+ℕ-succ zero n = refl
+ℕ-succ (suc m) n = cong suc (+ℕ-succ m n)

+ℕ-comm : ∀ (m n : ℕ) -> m +ℕ n ≡ n +ℕ m
+ℕ-comm m zero rewrite +ℕ-zlemma m = refl
+ℕ-comm m (suc n) rewrite +ℕ-succ m n | +ℕ-comm m n = refl

ℕ₊-commutative-monoid : commutative-monoid ℕ _+ℕ_ 0
ℕ₊-commutative-monoid = record
  { m = ℕ₊-monoid
  ; commutative = +ℕ-comm
  }

ℕ₊-semiring : semiring ℕ _+ℕ_ _*ℕ_ 0 1
ℕ₊-semiring = record
  { +-comm-monoid = ℕ₊-commutative-monoid
  ; x-monoid = {!   !}
  ; l-distₓ = {!   !}
  ; r-distₓ = {!   !}
  ; l-e₊-annihilateₓ = {!   !}
  ; r-e₊-annihilateₓ = {!   !}
  }
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

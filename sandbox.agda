module sandbox where
open import Data.List.Base using (List ; _∷_ ; [] ; foldr ; foldl ; map ; _++_ ; inits ; length ; replicate ; zipWith)
open import Data.Product using (_×_ ; _,_)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool ; true ; false)
open import Agda.Builtin.Nat renaming (_<_ to _l_ ; _+_ to _+ℕ_ ; _*_ to _xℕ_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong)
open Relation.Binary.PropositionalEquality.Core.≡-Reasoning


{-
data String : Set where thing : String

module ToString (T : Set) where
  toString : T -> String
  toString _ = thing

module Show {T : Set} (ev : (ToString T)) where
  open ToString ev
  show : T ->  String
  show t = toString t
-}



module Sort (A : Set)(_≤_ : A → A → Bool) where
  sort : List A -> List A
  sort = λ z → z

compare : ℕ -> ℕ -> Bool
compare x x₁ = false


module Sortℕ  = Sort ℕ compare

open Sortℕ

_ : List ℕ -> List ℕ
_ = sort





not : Bool -> Bool
not = {!   !}










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



x : ℕ
x = 4

m' : ℕ -- 2
m' = suc (suc zero)

n' : ℕ -- 3
n' = suc (suc (suc zero))

_ : n' ≡ n'
_ = refl

ex : ∀ (n m : ℕ) -> m +ℕ n ≡ m +ℕ n
ex n m = refl


+ℕ-assoc : ∀ (a b c : ℕ) -> (a +ℕ b) +ℕ c ≡ a +ℕ (b +ℕ c)
+ℕ-assoc zero n p = refl
+ℕ-assoc (suc m) n p = cong suc (+ℕ-assoc m n p)

+ℕ-zlemma : ∀ (n : ℕ) -> n +ℕ 0 ≡ n
+ℕ-zlemma zero = refl
+ℕ-zlemma (suc m) = cong suc (+ℕ-zlemma m)


-- THING


+ℕ-succ : ∀ (m n : ℕ) -> m +ℕ (suc n) ≡ suc (m +ℕ n)
+ℕ-succ zero n = refl
+ℕ-succ (suc m) n = cong suc (+ℕ-succ m n)

+ℕ-comm : ∀ (m n : ℕ) -> m +ℕ n ≡ n +ℕ m
+ℕ-comm m zero rewrite +ℕ-zlemma m = refl
+ℕ-comm m (suc n) rewrite +ℕ-succ m n | +ℕ-comm m n = refl


-- THING


ℕₓ-r-unit : ∀ (n : ℕ) -> n xℕ 1 ≡ n
ℕₓ-r-unit zero = refl
ℕₓ-r-unit (suc n) = cong suc (ℕₓ-r-unit n)

lemma : ∀ (n : ℕ) -> suc (1 xℕ n) ≡ 1 xℕ (suc n)
lemma zero = refl
lemma (suc n) = refl

ℕₓ-l-unit : ∀ (n : ℕ) -> 1 xℕ n ≡ n
ℕₓ-l-unit zero = refl
ℕₓ-l-unit (suc n) =
  begin
    1 xℕ suc n
  ≡⟨⟩
    (suc n) +ℕ  0 xℕ (suc n)
  ≡⟨⟩
    (suc n) +ℕ 0
  ≡⟨ +ℕ-zlemma (suc n) ⟩
    (suc n)
  ∎

xℕ-assoc : ∀ (x y z : ℕ) -> (x xℕ y) xℕ z ≡ x xℕ (y xℕ z)
xℕ-assoc x zero z = begin
    (x xℕ zero xℕ z)
    ≡⟨⟩
    {! refl  !}
xℕ-assoc x (suc y) z = begin
    (x xℕ (suc y)) xℕ z
  ≡⟨⟩
    {! relf  !}
--    ((suc x) xℕ y) xℕ z-
--  ≡⟨⟩
--    (y +ℕ x xℕ y) xℕ z
--  ≡⟨⟩
--   {! refl  !}



lemma₂ : ∀ (n : ℕ) -> n xℕ 0 ≡ 0
lemma₂ zero = refl
lemma₂ (suc n) = lemma₂ n



ℕ₊-monoid : monoid ℕ _+ℕ_ 0
ℕ₊-monoid = record
  { assoc = +ℕ-assoc
  ; l-unit = λ (a : ℕ) -> refl
  ; r-unit = +ℕ-zlemma
  }


ℕₓ-monoid : monoid ℕ _xℕ_ 1
ℕₓ-monoid = record
  { assoc = {!   !}
  ; l-unit = ℕₓ-l-unit
  ; r-unit = ℕₓ-r-unit
  }

ℕ₊-commutative-monoid : commutative-monoid ℕ _+ℕ_ 0
ℕ₊-commutative-monoid = record
  { m = ℕ₊-monoid
  ; commutative = +ℕ-comm
  }

-- THING
ℕ₊-semiring : semiring ℕ _+ℕ_ _xℕ_ 0 1
ℕ₊-semiring = record
  { +-comm-monoid = ℕ₊-commutative-monoid
  ; x-monoid = ℕₓ-monoid
  ; l-distₓ = {!   !}
  ; r-distₓ = {!   !}
  ; l-e₊-annihilateₓ = λ (n : ℕ) -> refl
  ; r-e₊-annihilateₓ = λ (n : ℕ) -> lemma₂ n
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
n ⋆ (coef (x ∷ xs)) = (n xℕ x) :: (n ⋆ (coef xs))

-- poly poly mult
_*_ : ℕ[X] -> ℕ[X] -> ℕ[X]
(coef xs) * (coef ys) = let result = map (λ (x : ℕ) -> out ( x ⋆ (coef ys))) xs
                            zeroPad = inits (replicate (length result) 0)
                            shifted = map coef (zipWith _++_ zeroPad result)
                        in foldl _+_ (coef []) shifted

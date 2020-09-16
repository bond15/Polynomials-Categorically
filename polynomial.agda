module polynomial where
open import Level
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

fiber : {ℓ : Level} -> (E : Set ℓ) -> (B : Set ℓ) -> (f : E -> B) -> (b : B) -> Set ℓ
fiber E B f b = Σ E (λ e -> (f e ≡ b))

record poly {ℓ}(E B : Set ℓ): Set (suc ℓ) where
 field
  rep : E -> B
  polynomial : (X : Set ℓ) -> Σ B (λ b -> fiber E B rep b -> X)

-- Problem 1: have to aditionally pull a random map from somewhere of type Eb -> X
-- Problem 2: can't represent empty fibers

data Unit : Set where
  unit : Unit

data ℕ : Set where
  z : ℕ
  s : ℕ -> ℕ

data Bool : Set where
  tt ff : Bool

data Empty : Set where

_ : poly Empty Bool
_ = record
  { rep = λ ()
  ; polynomial = λ X -> {!   !} }


f : Bool -> ℕ
f tt = z
f ff = s z

test : Σ Bool (λ (b : Bool) -> f b ≡ (s (s z)) )
test = tt , {!   !}

_ : poly Bool ℕ
_ = record
  { rep = λ { tt -> z ; ff -> (s z) }
  ; polynomial = λ X -> (s z) , {!   !}
  }

data _+_ {ℓ}(A B : Set ℓ) : Set ℓ where
  inj₁ : A -> A + B
  inj₂ : B -> A + B

_+map_ : {ℓ : Level} -> {A B C D : Set ℓ} -> (f : A -> B) -> (g : C -> D) -> A + C -> B + D
f +map g = λ { (inj₁ a) -> inj₁ (f a) ; (inj₂ b) ->  inj₂ (g b) }

_⊞_  : {ℓ : Level} -> {X Y A B : Set ℓ} -> poly X Y -> poly A B -> poly (X + A) (Y + B)
p ⊞ q = record
  { rep = (poly.rep p) +map (poly.rep q)
  ; polynomial = λ X -> {!  !}
  }

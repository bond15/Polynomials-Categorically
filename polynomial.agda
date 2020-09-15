module polynomial where
open import Level
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

fiber : {ℓ : Level} -> (B : Set ℓ) -> (E : Set ℓ) -> (f : E -> B) -> (b : B) -> Set ℓ
fiber X Y f b = Σ Y (λ e -> (f e ≡ b))

record poly {ℓ}(E B : Set ℓ): Set (suc ℓ) where
 field
  rep : E -> B
  polynomial : (X : Set ℓ) -> Σ B (λ b -> fiber B E rep b -> X)

data _+_ {ℓ}(A B : Set ℓ) : Set ℓ where
  inj₁ : A -> A + B
  inj₂ : B -> A + B

_+map_ : {ℓ : Level} -> {A B C D : Set ℓ} -> (f : A -> B) -> (g : C -> D) -> A + C -> B + D
f +map g = λ { (inj₁ a) -> inj₁ (f a) ; (inj₂ b) ->  inj₂ (g b) }

_⊞_  : {ℓ : Level} -> {X Y A B : Set ℓ} -> poly X Y -> poly A B -> poly (X + A) (Y + B)
p ⊞ q = record
  { rep = (poly.rep p) +map (poly.rep q)
  ; polynomial = {!   !}
  }

module poly where
open import Agda.Builtin.Sigma
open import Level
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

fiber : {ℓ : Level} -> (B : Set ℓ) -> (E : Set ℓ) -> (f : E -> B) -> (b : B) -> Set ℓ
fiber X Y f b = Σ Y (λ e -> (f e ≡ b))

record poly {ℓ}(E B : Set ℓ): Set (suc ℓ) where
 field
  rep : E -> B
  polynomial : (X : Set ℓ) -> Σ B (λ b -> fiber B E rep b -> X)

-- repackage as a record?
-- A Set polynomial represented by a Set map
-- polynomial : {B E : Set} -> (p : E -> B) -> Set -> Set
--polynomial {B} {E} p = λ (X : Set) -> Σ B (λ b -> fiber p b -> X)

_∘_ : {X Y Z : Set} -> (f : Y -> Z) -> (g : X -> Y) -> X -> Z
_∘_ f g x = f(g(x))

polynomialFmap : {B E X Y : Set} -> (p : E -> B) -> (f : X -> Y) -> polynomial p X -> polynomial p Y
polynomialFmap p f = λ { ( b , g ) -> ( b , f ∘ g ) }

-- Example
data Bool : Set where
  tt ff : Bool

data ℕ : Set where
  z : ℕ
  s : ℕ -> ℕ

not : Bool -> Bool
not tt = ff
not ff = tt

even : ℕ -> Bool
even z = tt
even (s n) = not (even n)


-- an element of a fiber is an element of the domain Set
-- paired with a proof that it is in the fiber
_ : fiber even tt
_ =  z , refl

const : ℕ -> Bool
const _ = ff

-- the first element of the pair determines which "sum term" to project into
-- the second element of the pair specifies the map
_ : polynomial even Bool
_ = tt , λ e -> const (fst e)


data Unit : Set where
  unit : Unit


x : Bool -> Unit
x _ = unit

-- polynomialFmap example
_ : polynomial even Bool -> polynomial even Unit
_ = polynomialFmap even x

data _+_ (A B : Set) : Set where
  inj₁ : A -> A + B
  inj₂ : B -> A + B

_+map_ : {A B C D : Set} -> (f : A -> B) -> (g : C -> D) -> A + C -> B + D
f +map g = λ { (inj₁ a) -> inj₁ (f a) ; (inj₂ b) ->  inj₂ (g b) }

--_+poly_ : {E F B C X : Set} -> (p : E -> B) -> (q : F -> C) -> polynomial p X -> polynomial q X -> polynomial (p +map q) X
--_+poly_ p q (e , ee) (f , ff) = {!   !}


-- P(1) ≅ B  where p : E -> B is the representing map
-- ∀ (p : E -> B) -> polynomial p Unit ≅ B

-- TODO develop equations for isomorphism reasoning


--

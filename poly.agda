module poly where
open import Agda.Builtin.Sigma
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

fiber : {B E : Set} -> (f : E -> B) -> (b : B) -> Set
fiber {B} {E} f b = Σ E (λ e -> (f e ≡ b))

-- A Set polynomial represented by a Set map
polynomial : {B E : Set} -> (p : E -> B) -> Set -> Set
polynomial {B} {E} p = λ (X : Set) -> Σ B (λ b -> fiber p b -> X)

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







-- TODO develop equations for isomorphism reasoning


--

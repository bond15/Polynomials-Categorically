module container where
open import Level
open import Data.Product as Prod using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)

-- Definition from Agda Standard Library
-- Papers

-- https://www.researchgate.net/publication/220444961_for_Data_Differentiating_Data_Structures
-- \rhd
infix 5 _▷_
record Containerℓ (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p


record Container₁ : Set₁ where
  constructor _▷₁_
  field
    Shape₁    : Set
    Position₁ : Shape₁ → Set


record Container₂ : Set₁ where
  constructor _▷₂_,_
  field
    Shape₂ : Set
    Pos₀ : Shape₂ -> Set
    Pos₁ : Shape₂ -> Set

-- The semantics ("extension") of a container.

-- P X = Σ (b ∈ B) (E b -> X)
-- in the other representation the underlying map induced a polynomial
-- p : E -> B is the representing map where E b denotes the fiber p⁻¹(b)
--  so E = Σ (b ∈ B) E b

⟦_⟧ℓ : ∀ {s p ℓ} → Containerℓ s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ℓ X = Σ[ s ∈ S ] (P s → X)

⟦_⟧₁ : Container₁ -> Set -> Set
⟦ S ▷₁ P ⟧₁ X = Σ[ s ∈ S ] (P s -> X)

⟦_⟧₂ : Container₂ -> Set -> Set -> Set
⟦ S ▷₂ P₁ , P₂ ⟧₂ X Y = Σ[ s ∈ S ] ((P₁ s -> X) × (P₂ s -> X)) -- not coproduct?


data Zero : Set where

record One : Set where
  constructor <>

data Two : Set where
  tt ff : Two


List : Container₁
List = ℕ ▷₁ (λ n -> Fin n)

List-Two : Set
List-Two = ⟦ List ⟧₁ Two

_ : List-Two
_ = ( 3 , λ { fzero ->  tt ;
              (fsuc fzero) -> ff ;
              (fsuc (fsuc fzero)) -> tt } )


-- constant
K : Set -> Container₁
K C = C ▷₁ λ _ -> Zero


_ : ⟦ K Two ⟧₁ One
_ = tt , λ ()

_ : ⟦ K Two ⟧₁ One
_ = ff , λ ()

One-c : Container₁
One-c = One ▷₁ λ _ -> One


_ : ⟦ One-c ⟧₁ Two
_ = <> , λ <> -> ff

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
    from∘to : ∀ (a : A) -> from (to a) ≡ a
    to∘from : ∀ (b : B) -> to (from b) ≡ b


_ : Two × (Zero -> One) ≃ Two
_ = record {
    to = proj₁
    ; from = λ x -> x , λ (z : Zero) -> <>
    ; from∘to = λ {( x , z) -> refl }
    ; to∘from = λ b -> refl
  }

absurd : {X : Set} -> Zero -> X
absurd ()

_ : (One × absurd) ≡ (One × absurd)
_ = ?


⟦KC⟧X≃C : {C X : Set}-> ⟦ K C ⟧₁ X ≃ C
⟦KC⟧X≃C {C}{X}= record {
     to = proj₁
   ; from = λ c -> c , absurd
   ; from∘to = λ { (c , abs) -> cong proj₁ {!   !} }
   ; to∘from = λ b -> refl
  }



⟦One-c⟧X≃X : {X : Set} -> ⟦ One-c ⟧₁ X ≃ X
⟦One-c⟧X≃X = record {
      to = λ p -> (proj₂ p) <>
    ; from = λ x -> <> , λ <> -> x
    ; from∘to = λ ( unit , f) -> refl
    ; to∘from = λ b -> refl
  }


-- --

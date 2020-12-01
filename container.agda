{-# OPTIONS --type-in-type #-} -- BAD NO NO NO BAD
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
    Shape₁    : Set -- B
    Position₁ : Shape₁ → Set -- E b


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
List = ℕ ▷₁ (λ n -> Fin n) -- n : ℕ ▷₁ Fin n

List-Two : Set
List-Two = ⟦ List ⟧₁ Two

_ : List-Two
_ = ( 3 , λ { fzero ->  tt ;
              (fsuc fzero) -> ff ;
              (fsuc (fsuc fzero)) -> tt } )


-- constant
K : Set -> Container₁
K C = C ▷₁ λ _ -> Zero
-- P X = Σ [ c ∈ C ] Zero -> X   .. Zero -> X ≡ λ()
-- Recall X⁰ = 1
-- P X ̄ = Σ [ c ∈ C ] 1
-- which is basically
-- P X = C
-- See ⟦KC⟧X≃C

_ : ⟦ K Two ⟧₁ One
_ = tt , λ ()

_ : ⟦ K Two ⟧₁ One
_ = ff , λ ()

Id : Container₁
Id = One ▷₁ λ _ -> One
-- P X = Σ [ c ∈ C ] E b -> X
-- P X = Σ [ e ∈ 1] 1 -> X
-- P X = 1 -> X     recall X¹ = X
-- P X = X
-- see ⟦Id⟧X≃X


_ : ⟦ Id ⟧₁ Two
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

--_ : (One × absurd) ≡ (One × absurd)
--_ = ?


⟦KC⟧X≃C : {C X : Set}-> ⟦ K C ⟧₁ X ≃ C
⟦KC⟧X≃C {C}{X}= record {
     to = proj₁
   ; from = λ c -> c , absurd
   ; from∘to = λ { (c , abs) -> {!   !} } --cong proj₁ {!   !} }
   ; to∘from = λ b -> refl
  }



⟦Id⟧X≃X : {X : Set} -> ⟦ Id ⟧₁ X ≃ X
⟦Id⟧X≃X = record {
      to = λ p -> (proj₂ p) <>
    ; from = λ x -> <> , λ <> -> x
    ; from∘to = λ ( unit , f) -> refl
    ; to∘from = λ b -> refl
  }

data _+_ (A B : Set) : Set where
  inj₁ : A -> A + B
  inj₂ : B -> A + B

-- Operations on Polynomial Functors, I mean containers..

_x_ : Container₁ -> Container₁ -> Container₁
(S ▷₁ P) x (T ▷₁ Q) = (S × T) ▷₁ (λ p -> P (proj₁ p) + Q (proj₂ p) )


_⊹_ : Container₁ -> Container₁ -> Container₁
(S ▷₁ P) ⊹ (T ▷₁ Q) = (S + T) ▷₁ λ { (inj₁ s) -> P s
                                   ; (inj₂ t) -> Q t }

_⇒_ : Set -> Container₁ -> Container₁
C ⇒ ( S ▷₁ P) = (C -> S) ▷₁ λ f -> Σ[ c ∈ C ] (P (f c))






-- --

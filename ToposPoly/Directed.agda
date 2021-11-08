module Directed where
open import Poly
open import Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;refl)

open import Agda.Builtin.Sigma

data Empty : Set where 

_-_ : (X : Set)(x : X) → Set
X - x = Σ X (λ x' → x ≡ x' → Empty)

data Bool : Set where 
    tt ff : Bool

-- inhabited since tt ≡ ff is not inhabited
_ : Bool - tt 
_ = ff , λ ()

-- Cannot construct since one must provide an inhabitant of Empty
_ : Bool - tt 
_ = tt , λ { refl → {!   !} }

--\partial
-- Derivative of Polynomial Functors
∂ : Poly → Poly
∂ (P ▹ D) = (Σ P D) ▹ λ{ (p , d) → (D p - d)}

K◂ : Set → Poly
K◂ A = A ▹ (λ _ → Empty)

I◂ : Poly 
I◂ = Unit ▹ λ _ → Unit


_ : ⦅ ∂ (K◂ Bool) ⦆ Unit 
_ = (tt , {!   !}) , {!   !}

_ : ⦅ ∂ I◂ ⦆ Unit 
_ = (unit , unit) , λ x → unit



--r : {A : Set} → Set 
--r {A} = (∂ (K◂ A)) ≈ K◂ Empty 



-- how does this related to McBrides implemntation of Poly derivates?
-- See ConCom pulled from his Github
record Dir ( 𝒫 : Poly) : Set where
    open Poly.Poly 𝒫 renaming (pos to S ; dir to P)
    field
        _↓_ : ∀ (s : S) → (P s → S)
        ⊛ : ∀ {s : S} → P s
        _⊕_ : ∀ {s : S}(p : P s) → P (s ↓ p) → P s

        --rules
        r1 : ∀{s : S} → ( s ↓ ⊛)  ≡ s 
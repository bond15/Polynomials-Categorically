module Directed where
open import Poly
open import Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

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
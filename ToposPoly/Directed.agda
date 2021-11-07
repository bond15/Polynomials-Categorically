module Directed where
open import Poly
open import Base

record Dir ( 𝒫 : Poly) : Set where
    open Poly.Poly 𝒫 renaming (pos to S ; dir to P)
    field
        _↓_ : ∀ (s : S) → (P s → S)
        ⊛ : ∀ {s : S} → P s
        _⊕_ : ∀ {s : S}(p : P s) → P (s ↓ p) → P s

        --rules
        r1 : ∀{s : S} → ( s ↓ ⊛)  ≡ s
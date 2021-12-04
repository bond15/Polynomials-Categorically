module Ex where 

data Unit : Set where 
    unit : Unit
data Bool : Set where 
    tt ff : Bool

nand : Bool → Bool → Bool 
nand tt tt = ff
nand _ _ = tt

open import Poly
open import Data.Product

-- A wiring diagram box
-- Output: Bool
-- Input: Bool × Bool
NandBox : Poly
NandBox = Bool ▹ (λ _ → Bool × Bool)

-- A wiring diagram box
-- Output: Bool
-- Input: Bool
NotBox : Poly
NotBox = Bool ▹ (λ _ → Bool)

-- Definition of a System
-- Systems "implement the interface" of a wiring diagram
-- S is the internal state type
-- p is the interface
record Sys(S : Set)(p : Poly): Set where
        constructor Syˢ⇒_
        field
            --a systme is a morphism of polynomials
            system : Poly[ S ▹ (λ _ → S) , p ]
open Sys

-- Implements the internal of the Nand box
Nand : Sys Bool NandBox
Nand = Syˢ⇒ ((λ x → x) ⇒ₚ (λ{ _ (b₁ , b₂) → nand b₁ b₂}))

-- Describes a mapping between wiring diagrams
-- how to map inputs and internal state to inputs
-- how to map outputs to outputs
wrap : Poly[ NandBox , NotBox ]
wrap = (λ x → x) ⇒ₚ λ _ x → x , x

-- An operation to fill in a wiring diagram given
-- An existing implementation for interface p
-- A rewiring map from interface p to interface q
_∘ₛ_ : {S : Set} {p q : Poly} → Sys S p → Poly[ p , q ] → Sys S q
(Syˢ⇒ f) ∘ₛ g = Syˢ⇒ (f ⇒∘ₚ g)

-- An implementation of Not using Nand and rewiring
Not : Sys Bool NotBox
Not = Nand ∘ₛ wrap
module Wtypes where
open import Poly
open import Base
open import Agda.Builtin.Sigma

-- well founded trees
data 𝓦 (P : Poly) : Set where
    ⟨_⟩ : ⦅ P ⦆ (𝓦 P) → 𝓦 P

data Nada : Set where

-- 0 + 1
NatP : Poly
NatP = Pos₂ ▹ λ{  P₁ → Nada 
                ; P₂ → Unit }

Nat : Set 
Nat = 𝓦 NatP

zero : Nat
zero = ⟨ P₁ , (λ ()) ⟩

Suc : Nat → Nat
Suc n = ⟨ (P₂ , λ{ unit → n}) ⟩

Three : Nat 
Three = Suc (Suc (Suc zero))
open import Data.Product

-- Binary trees
BinP : Set → Poly
BinP X = Pos₂ ▹ λ { P₁ → Nada
                  ; P₂ → Unit × X × Unit}

BinT : Set → Set 
BinT X = 𝓦 (BinP X)

data Bool : Set where 
    tt ff : Bool
    
BoolTree : Set 
BoolTree = BinT Bool

Leaf : BoolTree
Leaf = ⟨ P₁ , (λ()) ⟩

-- not quite right...
-- feels like an elliminator instead of a constructor
Node : BoolTree → Bool → BoolTree → BoolTree
Node l b r = ⟨ (P₂ , λ { (d₁ , d₂ , d₃) → r}) ⟩
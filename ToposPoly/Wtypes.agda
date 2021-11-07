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
module Types where

-- This work is following Bob Atkey
-- https://gist.github.com/bobatkey/0d1f04057939905d35699f1b1c323736
open import Poly
open Poly.Poly
--
{-
    recall Poly
        pos : Set 
        dir : pos -> Set
-}

-- Ty Γ ≔ Γ .pos → Poly ??
record Ty (Γ : Poly) : Set₁ where 
    field 
        q : Γ .pos → Set 
        r : (γ : Γ .pos) → q γ → Set 
open Ty

{- recall
record Poly[_,_](p q : Poly) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
-}

record Tm (Γ : Poly) (S : Ty Γ) : Set where 
    field 
        mor : (γ : Γ .pos) → (S .q) γ
        rom : (γ : Γ .pos) → (S .r) γ (mor γ) → (Γ .dir) γ
-- 1/29/22
-- no clue wtf is going on here
-- I guess Poly is also a CwF so can be used to model dependent types?
-- .. come back to this
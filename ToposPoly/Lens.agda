{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Lens where

open import Agda.Builtin.Sigma
open import Data.Product 
open import Poly
open import Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)
open import Category

open Poly.Poly[_,_]

-- 2.3.3
    -- Lenses are morphisms between monomials
--data Lens a b s t = Lens { view :: s -> a, update :: (b ,s) -> t}

-- Haskell Lens
record Lens' (S T A B : Set ): Set where
    field   
        view : S → A
        update : B × S → T

open Lens'

-- Lense are just morphisms of monomials  
-- Syᵀ → Ayᴮ
Lens : Set → Set → Set → Set → Set
Lens S T A B = Poly[ S ▹ (λ _ →  T) , A ▹ (λ _ → B) ]

-- These definitions of Lenses are isomorphic
lemma-LensIso : {S T A B : Set} → Lens' S T A B ≈ Lens S T A B 
lemma-LensIso = record { 
    to = λ x → record { onPos = view x ; onDir = λ i x₁ → update x (x₁ , i) } ; 
    from = λ x → record { view = onPos x ; update = λ { (fst₁ , snd₁) → onDir x snd₁ fst₁ }} ; 
    from∘to = λ x → refl ; 
    to∘from = λ y → refl 
    }


-- Examples of Lenses
{-
p1 :: Lens a b (a,c) (b,c)
p1 = Lens view update where
    view (x,y) = x
    update (x', (x,y)) = (x',y)

-}
-- Haskell
hlens : {A B C : Set } → Lens' (A × C) (B × C) A B 
hlens = record { 
    view = fst ; 
    update = λ (b , a , c) → (b , c)
    }

-- monomial lens
plens : {A B C : Set} → Lens (A × C) (B × C) A B
plens =  record { 
            onPos = λ { (a , c) → a };  -- view
            onDir = λ { (a , c) → λ b → b , c }  --update
            }

-- monomials and Lenses form the category of bimorphic lenses!
-- https://arxiv.org/abs/1808.05545

Lens∘ : { S T A B C D : Set } → Lens S T A B → Lens A B C D → Lens S T C D
Lens∘ p q = p ∘ₚ q


record _≋L_ {S T A B : Set} (f g : Lens S T A B) : Set where
    field
        eq-pos : onPos f ≡ onPos g
        eq-dir : onDir f ≡ onDir g

Bimorphic : Category
Bimorphic = record
                { Ob = Set × Set
                ; _⇒_ = λ { (S , T) → λ { (A , B) → Lens S T A B} }
                ; _≋_ = _≋L_
                ; _∘_ = λ  p q → q ∘ₚ p -- composition of polynomails (applied here to the specific case of monomials or Lenses)
                ; id = record { onPos = λ z → z ; onDir = λ i z → z }
                ; idˡ = λ f₁ → refl
                ; idʳ = λ f₁ → refl
                ; ∘-assoc = λ f₁ g h → refl
                }
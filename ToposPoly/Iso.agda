module Iso where
open import Base 
open _≈_

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

module ≈-Reasoning where

≈-refl : ∀ {A : Set}
    -----
  → A ≈ A
≈-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }


≈-trans : ∀ {A B C : Set}
  → A ≈ B
  → B ≈ C
    -----
  → A ≈ C
≈-trans A≈B B≈C =
  record
    { to       = to   B≈C o to   A≈B
    ; from     = from A≈B o from B≈C
    ; from∘to  = λ{x →
        begin
          (from A≈B o from B≈C) ((to B≈C o to A≈B) x)
        ≡⟨⟩
          from A≈B (from B≈C (to B≈C (to A≈B x)))
        ≡⟨ cong (from A≈B) (from∘to B≈C (to A≈B x)) ⟩
          from A≈B (to A≈B x)
        ≡⟨ from∘to A≈B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≈C o to A≈B) ((from A≈B o from B≈C) y)
        ≡⟨⟩
          to B≈C (to A≈B (from A≈B (from B≈C y)))
        ≡⟨ cong (to B≈C) (to∘from A≈B (from B≈C y)) ⟩
          to B≈C (from B≈C y)
        ≡⟨ to∘from B≈C y ⟩
          y
        ∎}
     }

infix  1 ≈-begin_
infixr 2 _≈⟨_⟩_
infix  3 _≈-∎

≈-begin_ : ∀ {A B : Set}
    → A ≈ B
      -----
    → A ≈ B
≈-begin A≈B = A≈B

_≈⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≈ B
    → B ≈ C
      -----
    → A ≈ C
A ≈⟨ A≈B ⟩ B≈C = ≈-trans A≈B B≈C

_≈-∎ : ∀ (A : Set)
      -----
    → A ≈ A
A ≈-∎ = ≈-refl

open ≈-Reasoning
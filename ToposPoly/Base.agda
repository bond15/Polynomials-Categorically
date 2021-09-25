{-# OPTIONS --without-K #-}
module Base where


open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
open import Data.Fin.Base using (Fin ; suc; zero ; fromℕ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Agda.Builtin.Sigma 

infix 0 _≈_
record _≈_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≈_



data Unit : Set where
    unit : Unit

eq-Σ : { I X : Set} → (e1 e2 : Σ I (λ _ → X )) → fst e1 ≡ fst e2 →  snd e1 ≡ snd e2 → e1 ≡ e2 
eq-Σ (i,f) (i',f') ieq feq = cong₂ _,_ ieq feq

-- Axiom
postulate
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g
postulate 
  Extensionality : {A : Set } {B : A → Set } {f g : (x : A) → B x} 
    → (∀ x → f x ≡ g x) → f ≡ g


lemma-funit : {A : Set} → (f :  A → Unit) → ( a : A )  → f a ≡ unit
lemma-funit f a with f a
...               | unit = refl

lemma-thing : {A : Set} → (f :  A → Unit) → ( a : A )  → f a ≡ unit → f ≡ (λ _ → unit )
lemma-thing f _ _ = extensionality λ a → lemma-funit f a

_؛_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ؛ g = λ x → g(f x)

_o_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g o f = λ x → g(f x)


data Dir₀ : Set where
data Dir₁ : Set where
    D₁ : Dir₁
data Dir₂ : Set where
    D₁ D₂ : Dir₂
data Dir₃ : Set where
    D₁ D₂ D₃ : Dir₃
data Dir₄ : Set where
    D₁ D₂ D₃ D₄ : Dir₄

data Pos₁ : Set where
    P₁ : Pos₁
data Pos₂ : Set where
    P₁ P₂ : Pos₂
data Pos₃ : Set where
    P₁ P₂ P₃ : Pos₃
data Pos₄ : Set where
    P₁ P₂ P₃ P₄ : Pos₄
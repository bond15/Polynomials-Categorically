module OrnCat where 

record IPoly(J I : Set) : Set₁ where
    constructor _◂_𝒾_
    field 
        S : J → Set 
        P : {j : J} → S j → Set
        n : {j : J}{sh : S j} → P sh → I
         
open IPoly

open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Function

⦅_⦆ : {J I : Set} → IPoly J I → (X : I → Set) → J → Set 
⦅ S ◂ P 𝒾 n ⦆ X = λ j → (Σ[ sh ∈ S j ] (∀(pos : P sh) → X (n pos))) 


ℕ-Poly : IPoly ⊤ ⊤ 
ℕ-Poly = (λ tt → ⊤ ⊎ ⊤) ◂ (λ{ (inj₁ tt) → ⊥
                       ; (inj₂ tt) → ⊤}) 𝒾 λ _ → tt

ℕ : Set 
ℕ = ⦅ ℕ-Poly ⦆ (λ{tt → ⊤}) tt

z : ℕ 
z = (inj₁ tt) , λ()

s : ℕ → ℕ
s m = (inj₂ tt) , id

_ : ℕ
_ = s (s z)

List-Poly : (X : Set) → IPoly ⊤ ⊤
List-Poly X = (λ{tt → ⊤ ⊎ X}) ◂ (λ{(inj₁ x) → ⊥
                                ; (inj₂ y) → ⊤}) 𝒾 λ{_ → tt}

List : Set → Set 
List X = ⦅ List-Poly X ⦆ (λ{ tt → ⊤ }) tt

nil : {X : Set} → List X 
nil = (inj₁ tt) , λ ()

cons : {X : Set} → X → List X → List X 
cons x xs = (inj₂ x) , id

_ : List Bool 
_ = cons true (cons false nil)


open import Data.Nat renaming (ℕ to 𝕟)
Vec-Poly : (X : Set) → IPoly 𝕟 𝕟 
Vec-Poly X = (λ{zero → ⊤
              ; (suc x) → X}) 
              
            ◂ (λ { {j = zero} x → ⊥
                 ; {j = suc n} x → ⊤}) 
                 
            𝒾 λ{ {j = suc n} tt → n}


Vec : Set → 𝕟 → Set
Vec X n = ⦅ Vec-Poly X ⦆ {!   !} n -- not sure if this is correct I J values..

vnil : {X : Set}{n : 𝕟} → Vec X n 
vnil = {!   !} , {!   !}



--Vec-Poly : (X : Set) → IPoly ℕ ℕ 
--Vec-Poly X = (λ{(inj₁ tt , _) → ⊤
--              ; (inj₂ tt , _) → X}) ◂ (λ{ {j = inj₁ zero , _} tt → ⊥
 --                                       ; {j = inj₂ sucn , _} x → ⊤}) 𝒾 λ{ {j = inj₂ sucn , n} {sh = sh} x → inj₁ tt , (λ x → tt)}


 -- lemma - Poly ≅ IPoly ⊤ ⊤ ?

{-
  Polynomial
    Category C
      A,B,I,J : Obj C 

      s : B → I 
      f : B → A 
      t : A → J

      so

      I ← B → A → J
        s   f   t
-}

{-
  Polynomial Functor

  interpret a polynomial in ε into a functor between slices of ε

  F : I ← B → A → J 
        s   f   t
  to 

  PF  : ε/I → ε/B → ε/A → ε/J
            Δs    Πf    Σt

        where Σt ≔ f ∘ _ 
        and 
              Δs ≔ first projection of fiberproduct (in set)? (pullback)
                    change base functor


  so a functor F is polynomial if it is isomorphic to the interpretation of a polynomial
    ex
      there exists s,f,and t  such that  F ≅ Σt Πf Δs
-}  


{- 
  ε : LCCC

  the "internal language"
    still don't understand what this phrase means
  
  the internal language is a type theory

  a container is a polynomial expressed in the internal language of ε
    IPoly
  
  the interpretation is expressed in the internal language ??
    by ⦅ ⦆ 
-}
open import Agda.Builtin.Equality
record CartMorCont {I J K L : Set} 
                   (IP₁ : IPoly J I)(IP₂ : IPoly L K)
                   (v : J → L)(u : I → K): Set where
  private
    module P₁ = IPoly IP₁
    module P₂ = IPoly IP₂
    open P₁ renaming (S to S₁ ; P to P₁ ; n to n₁)
    open P₂ renaming (S to S₂ ; P to P₂ ; n to n₂)
  field 
    σ : {j : J} → S₁ j → S₂ (v j)
    ρ : {j : J} → ∀ (sh : S₁ j) → {! P₂ ?  !} ≡ {!   !}

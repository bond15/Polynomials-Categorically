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
                 ; {j = suc j} x → ⊤}) 
                 
            𝒾 λ{ {j = suc n} tt → n}


Vec : Set → 𝕟 → Set
Vec X n = ⦅ Vec-Poly X ⦆ {!   !} n -- not sure if this is correct I J values..

vnil : {X : Set}{n : 𝕟} → Vec X n 
vnil = {!   !} , {!   !}



--Vec-Poly : (X : Set) → IPoly ℕ ℕ 
--Vec-Poly X = (λ{(inj₁ tt , _) → ⊤
--              ; (inj₂ tt , _) → X}) ◂ (λ{ {j = inj₁ zero , _} tt → ⊥
 --                                       ; {j = inj₂ sucn , _} x → ⊤}) 𝒾 λ{ {j = inj₂ sucn , n} {sh = sh} x → inj₁ tt , (λ x → tt)}
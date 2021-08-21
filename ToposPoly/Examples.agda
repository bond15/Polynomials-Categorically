{-# OPTIONS --type-in-type #-}
module Examples where

open import Poly
open Poly.Poly
open import Base
open import Data.Nat
open import Data.Product
open import Agda.Builtin.Sigma
open import Data.List
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
open import Data.Fin.Base using (Fin ; suc; zero ; fromℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)

-- y² + 2y + 1
ex : Poly
ex = record { pos = Fin 4 ; dir = λ { zero → Fin 0 
                                ; (suc zero) → Fin 1 
                                ; (suc (suc zero )) → Fin 1 
                                ; (suc (suc (suc zero))) → Fin 2 }}


-- y² + 1
ex2 : Poly
ex2 = record { pos = Fin 2 ; dir = λ {zero → Fin 0
                                    ; (suc zero) → Fin 2} }


_ : Poly
_ = ex ×ₚ ex


pp : Poly -- y² + 1
pp = record { pos = Pos₂ ; dir = λ{ P₁ → Dir₂
                                 ; P₂ → Dir₀ }}


-- evaluating PP ℕ = ℕ² + 1 =  ℕ × ℕ + 1
-- so choose a pair 
_ : ⦅ pp ⦆ ℕ
_ = P₁ , λ{ D₁ → 4
          ; D₂ → 7 }
-- or chose none!          
_ : ⦅ pp ⦆ ℕ
_ = P₂ , λ ()


data Foo : Set where
    Bar Baz : Foo

-- enumerate all elements of ⦅ pp ⦆ Foo
-- ≅ Option (Foo × Foo)
_ : List (⦅ pp ⦆ Foo)
_ = (P₁ , (λ { D₁ → Bar
            ; D₂ → Bar })) ∷ 
    (P₁ , (λ{ D₁ → Bar
            ; D₂ → Baz }))  ∷  
    (P₁ , (λ{ D₁ → Baz
            ; D₂ → Bar })) ∷ 
    (P₁ , (λ{ D₁ → Baz
            ; D₂ → Baz })) ∷ 
    (P₂ , λ()) ∷ []   



qq : Poly -- y² + 2y + 1
qq = record { pos = Pos₄ ; dir = λ{ P₁ → Dir₂
                                  ; P₂ → Dir₁
                                  ; P₃ → Dir₁
                                  ; P₄ → Dir₀ } }

_ : ⦅ qq ⦆ ℕ
_ = P₂ , λ{ D₁ → 7 }                                 

-- poly morphism from y² + 1 to y² + 2y + 1 (or y² + y + y + 1)
_ : Poly[ pp , qq ]
_ = record { onPos = λ{ P₁ → P₁
                      ; P₂ → P₄} ;  -- This maps positions y² to y² and 1 to 1
                      
             onDir = λ{ P₁ → λ{ D₁ → D₂
                              ; D₂ → D₁ } -- inverts the directions from qq's y² to pp's y²
                      ; P₂ → λ() }}       --   


-- another poly morphism from y² + 1 to y² + 2y + 1
_ : Poly[ pp , qq ]
_ = record { onPos = λ{ P₁ → P₂
                      ; P₂ → P₃ } -- maps to the 2 inner terms (ys)
           ; onDir = λ{ P₁ → λ{ D₁ → D₂ }
                      ; P₂ → λ{ D₁ →  {! !} }}} -- not possible to map from 1 direction to 0 directions!


𝕐 : Poly -- 1y¹ = y
𝕐 = record { pos = Pos₁ ; dir = λ x → Dir₁ }


-- enumerate all elements of pp (y² + 1)
_ : elem pp
_ = P₁ , D₁

_ : elem pp
_ = P₁ , D₂

_ : elem pp
_ = P₂ , {!   !} -- Can't represent the position with no directions..

_ : elem ex
_ = suc zero , zero

_ : elem (ex ⊎ₚ ex)
_ = inj₁ ((suc zero)) , zero

xx : Poly -- y³ + y
xx = record { pos = Pos₂ ; dir = λ{ P₁ → Dir₃
                                  ; P₂ → Dir₁ } }
yy : Poly -- y⁴ + y² + 1
yy = record { pos = Pos₃ ; dir = λ{ P₁ → Dir₄
                                  ; P₂ → Dir₂
                                  ; P₃ → Dir₀ } } 


-- xx × yy = y⁷ + y⁵ + y³ + y⁵ + y³ + y = y⁷ + 2y⁵ + 2y³ + y
xxyy : Poly
xxyy = xx ×ₚ yy

_ : elem xxyy
_ = (P₁ , P₁) , inj₂ D₃

_ : elem xxyy
_ = (P₂ , P₃) , inj₁ D₁

_ : elem xxyy
_ = (P₁ , P₃) , inj₁ D₂

_ : ⦅ xxyy ⦆ ℕ
_ = (P₁ , P₂) , λ{ (inj₁ D₁) → 1
                 ; (inj₁ D₂) → 2
                 ; (inj₁ D₃) → 3
                 ; (inj₂ D₁) → 4
                 ; (inj₂ D₂) → 5 }


-- Poly should also act on Functions from Set to Set
f : Foo → ℕ
f = λ{ Bar → 1
     ; Baz → 7 }

lf : ⦅ xx ⦆ Foo → ⦅ xx ⦆ ℕ
lf = lift xx f

xxfoo : ⦅ xx ⦆ Foo
xxfoo = P₁ , λ{ D₁ → Bar
              ; D₂ → Baz
              ; D₃ → Bar }

xxℕ : ⦅ xx ⦆ ℕ
xxℕ = P₁ , λ{ D₁ → 1
            ; D₂ → 7
            ; D₃ → 1 }

exx : ⦅ xx ⦆ ℕ 
exx = lf xxfoo


_ : exx ≡ xxℕ
_ = {! cong₂ ? ? !}



_ : {I : Set} → (I ≈ Σ I (λ _ → Unit))
_ = record { 
    to = λ i → i , unit ; 
    from = λ iu  → proj₁ iu ; 
    from∘to = λ i → refl ; 
    to∘from = λ{ (i , unit) → refl}}


_ : Poly ≈ Σ[ i ∈ Set ] ( i → Set)
_ = record { 
    to = λ { (pos₁ ▹ dir₁) → pos₁ , dir₁} ; 
    from = λ{ (fst₁ , snd₁) → fst₁ ▹ snd₁ }; 
    from∘to = λ { (pos₁ ▹ dir₁) → refl }; 
    to∘from = λ { (fst₁ , snd₁) → refl } }


-- recall qq =  y² + 2y + 1
_ : ⦅ qq ⦆ Unit
_ = P₁ , λ { D₁ → unit
           ; D₂ → unit }
-- P := Σ I (λ i → Set)
-- I ≈ ⦅ p ⦆ 1



Z : {p : Poly} → (pos p) ≈ ⦅ p ⦆ Unit -- the indexing set is isomorphic to the polynomial evaluated at 1, ex  p(y) = 2y² + 3y + 1  and p(1) = 2 + 3 + 1 = 7 
Z { p }  = record { 
    to = λ posp → posp , λ x → unit ; 
    from = λ{ pair → fst pair }; 
    from∘to = λ posp → refl ; 
    to∘from = λ { ( posp , posptoUnit) → {! cong₂ _,_ {posp} {posp} {λ _ → unit} ? ?!} }
    } 
data Zero : Set where

-- P(0) yields only the constants 
_ : ⦅ qq ⦆ Zero
_ = P₄ , λ ()
-- Syˢ → Tyᵗ







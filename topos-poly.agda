{-# OPTIONS --type-in-type #-}
module topos-poly where

open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
open import Data.Fin.Base using (Fin ; suc; zero ; fromℕ)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;cong₂;cong-app)

open import Agda.Builtin.Sigma 

infix 0 _≈_
record _≈_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≈_

-- Axiom
postulate
  extensionality : ∀ {A B : Set }{f g : A -> B}
    -> (∀ (x : A) -> f x ≡ g x)
    ---------------------------
    -> f ≡ g
postulate 
  Extensionality : {A : Set } {B : A → Set } {f g : (x : A) → B x} 
    → (∀ x → f x ≡ g x) → f ≡ g

_ : Fin 3
_ = fromℕ 2

record Poly : Set where
  field
    pos : Set
    dir : pos -> Set

open Poly

{-
Poly' : Set
Poly' = Σ Set (λ x -> Set)

_ : Poly'
_ = Fin 4 , {!   !}
-}



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


_ : (dir ex) (suc (suc (suc zero)))
_ = suc zero

_⊎ₚ_ : Poly → Poly → Poly
p ⊎ₚ q = record { pos = pos p ⊎ pos q ; dir = λ { (inj₁ x) → (dir p) x
                                                ; (inj₂ y) → (dir q) y } }

-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ
_×ₚ_ : Poly → Poly → Poly
p ×ₚ q = record { pos = pos p × pos q ; dir = λ {(i , j) → (dir p) i ⊎ (dir q) j} }

record Polyₓ (p q : Poly) : Set where
    field
        posₓ : pos p × pos q
        dirₓ : (pq : pos p × pos q) → (dir p) (fst pq) ⊎ (dir q) (snd pq) 

lemma-xₚ-polyₓ : {p q : Poly}
{-
Poly[_,_] : Poly → Poly → Set
Poly[ p , q ] = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ((dir q)j → (dir p)i))
-}

record Poly[_,_](p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Poly[_,_]
-- y² + 2y + 1 + y² + 2y + 1 = 2y² + 4y + 2
_ : Poly
_ = ex ×ₚ ex



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

pp : Poly -- y² + 1
pp = record { pos = Pos₂ ; dir = λ{ P₁ → Dir₂
                                 ; P₂ → Dir₀ }}
qq : Poly -- y² + 2y + 1
qq = record { pos = Pos₄ ; dir = λ{ P₁ → Dir₂
                                  ; P₂ → Dir₁
                                  ; P₃ → Dir₁
                                  ; P₄ → Dir₀ } }

-- poly morphism from y² + 1 to y² + 2y + 1 (or y² + y + y + 1)
_ : Poly[ pp , qq ]
_ = record { onPos = λ{ P₁ → P₁
                      ; P₂ → P₄} ;  -- This maps positions y² to y² and 1 to 1
                      
             onDir = λ{ P₁ → λ{ D₁ → D₂
                              ; D₂ → D₁ } -- inverts the directions from qq's y² to pp's y²
                      ; P₂ → λ() }}       --                    
                                  

_؛_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ؛ g = λ x → g(f x)

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f x)

-- another poly morphism from y² + 1 to y² + 2y + 1
_ : Poly[ pp , qq ]
_ = record { onPos = λ{ P₁ → P₂
                      ; P₂ → P₃ } -- maps to the 2 inner terms (ys)
           ; onDir = λ{ P₁ → λ{ D₁ → D₂ }
                      ; P₂ → λ{ D₁ →  {! !} }}} -- not possible to map from 1 direction to 0 directions!


𝕐 : Poly -- 1y¹
𝕐 = record { pos = Pos₁ ; dir = λ x → Dir₁ }

_∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) ∘ ((onDir qr) ((onPos pq) i)) } -- backward composition on directions


data Unit : Set where
    unit : Unit

Poly[] : Poly → Poly → Set
Poly[] p q = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ∀ (d : dir q j) → Σ (dir p i) λ c → Unit )


lemma-poly[]-iso : {p q : Poly} → Poly[] p q ≈ Poly[ p , q ]
lemma-poly[]-iso {p} {q} = record { to = λ p[] → record { onPos = λ ppos → fst( p[] ppos) ; onDir = λ ppos x → fst(snd(p[] ppos) x) } 
                        ; from = λ poly[p,q] ppos → (onPos poly[p,q]) ppos , λ d → (onDir poly[p,q]) ppos d , unit 
                        ; from∘to = λ poly[]pq → Extensionality {!   !}
                        ; to∘from = λ poly[p,q] → refl }

elem : Poly → Set
elem p = Σ (pos p) (dir p)

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

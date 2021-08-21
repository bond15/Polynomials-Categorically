{-# OPTIONS --type-in-type #-}
module topos-poly where

open import Data.List
open import Data.Product
open import Data.Nat
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


record Poly' (X : Set) : Set where

record Poly : Set where
  constructor _▹_
  field
    pos : Set
    dir : pos -> Set
open Poly

-- see container.agda

-- The semantics ("extension") of a container.

-- P X = Σ (b ∈ B) (E b -> X) = Σ B (λ b → E b → X)
-- in the other representation the underlying map induced a polynomial
-- p : E -> B is the representing map where E b denotes the fiber p⁻¹(b)
--  so E = Σ (b ∈ B) E b

⦅_⦆ : Poly → Set → Set
⦅ P ▹ D ⦆ X = Σ[ p ∈ P ] (D p → X)

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


{-
lemma-xₚ-polyₓ : {p q : Poly} → (p ×ₚ q) → Polyₓ p q
lemma-×ₚ-polyₓ = ?

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
                                  

_؛_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ؛ g = λ x → g(f x)

_o_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g o f = λ x → g(f x)

-- another poly morphism from y² + 1 to y² + 2y + 1
_ : Poly[ pp , qq ]
_ = record { onPos = λ{ P₁ → P₂
                      ; P₂ → P₃ } -- maps to the 2 inner terms (ys)
           ; onDir = λ{ P₁ → λ{ D₁ → D₂ }
                      ; P₂ → λ{ D₁ →  {! !} }}} -- not possible to map from 1 direction to 0 directions!


𝕐 : Poly -- 1y¹ = y
𝕐 = record { pos = Pos₁ ; dir = λ x → Dir₁ }

_∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) o ((onDir qr) ((onPos pq) i)) } -- backward composition on directions


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

_ : ⦅ xxyy ⦆ ℕ
_ = (P₁ , P₂) , λ{ (inj₁ D₁) → 1
                 ; (inj₁ D₂) → 2
                 ; (inj₁ D₃) → 3
                 ; (inj₂ D₁) → 4
                 ; (inj₂ D₂) → 5 }


_ : (X Y : Set) → Poly 
_ = λ X Y → (X → Y) ▹ λ f → {!   !}

lift : {X Y : Set} → (p : Poly) → (X → Y) → (⦅ p ⦆ X → ⦅ p ⦆ Y)
lift p f = λ{ (fst₁ , snd₁) → fst₁ , snd₁ ؛ f}
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
_ = {!   !}
{-}
_ : ⦅ Poly[ pp , qq ] ⦆ (Foo → ℕ)
_ = P₁ , λ{ D₁ → f
          ; D₂ → f}
          -}

_ : {I : Set} → (I ≈ Σ I (λ _ → Unit))
_ = record { to = λ i → i , unit ; from = λ iu  → proj₁ iu ; from∘to = λ i → refl ; to∘from = λ{ (i , unit) → refl}}


_ : Poly ≈ Σ[ i ∈ Set ] ( i → Set)
_ = record { to = λ { (pos₁ ▹ dir₁) → pos₁ , dir₁} ; from = λ{ (fst₁ , snd₁) → fst₁ ▹ snd₁ }; from∘to = λ { (pos₁ ▹ dir₁) → refl }; to∘from = λ { (fst₁ , snd₁) → refl } }


-- recall qq =  y² + 2y + 1
_ : ⦅ qq ⦆ Unit
_ = P₁ , λ { D₁ → unit
           ; D₂ → unit }
-- P := Σ I (λ i → Set)
-- I ≈ ⦅ p ⦆ 1
_ : {p : Poly} → (pos p) ≈ ⦅ p ⦆ Unit -- the indexing set is isomorphic to the polynomial evaluated at 1, ex  p(y) = 2y² + 3y + 1  and p(1) = 2 + 3 + 1 = 7 
_ = record { to = λ posp → posp , λ _ → unit ; from = λ{ (fst₁ , snd₁) → fst₁ }; from∘to = λ posp → refl ; to∘from = λ{ (fst₁ , snd₁) → {!!} }}

data Zero : Set where

-- P(0) yields only the constants 
_ : ⦅ qq ⦆ Zero
_ = P₄ , λ ()
-- Syˢ → Tyᵗ


yˢ : (S : Set) → Poly
yˢ S = Unit ▹ λ _ → S
--2.3.2

yoneda : {S : Set} → {q : Poly} → Poly[ yˢ S , q ] ≈ ⦅ q ⦆ S
yoneda =  record { to = λ{ record { onPos = onPos ; onDir = onDir } → onPos unit , λ x → onDir unit x } 
                    ; from = λ { (fst₁ , snd₁) → record { onPos = λ _ → fst₁ ; onDir = λ i → snd₁ } } 
                    ; from∘to = λ{ record { onPos = onPos ; onDir = onDir } → {! refl  !} } 
                    ; to∘from = λ { (fst₁ , snd₁) → refl } }


-- 2.3.3
    -- Lenses are morphisms between monomials
--data Lens a b s t = Lens { view :: s -> a, update :: (b ,s) -> t}
Lens : Set → Set → Set → Set → Set
Lens S T A B = Poly[ S ▹ (λ _ →  T) , A ▹ (λ _ → B) ]
{-
p1 :: Lens a b (a,c) (b,c)
p1 = Lens view update where
    view (x,y) = x
    update (x', (x,y)) = (x',y)

-}
_ : {A B C : Set} → Lens (A × C) (B × C) A B
_ =  record { 
            onPos = λ { (a , c) → a };  -- view
            onDir = λ { (a , c) → λ b → b , c }  --update
            }


-- monomails and Lense form the category of bimorphic lenses!
-- https://arxiv.org/abs/1808.05545


REL : Set -> Set  -> Set 
REL A B = A -> B -> Set 

Rel :  Set -> Set 
Rel A  = REL A A 

record Category : Set where
  field
    Ob : Set 
    _⇒_ : Rel Ob 
    _∘_  : ∀ {x y z : Ob} -> y ⇒ z -> x ⇒ y -> x ⇒ z
    id : ∀ {o : Ob} -> o ⇒ o
    idˡ : ∀ {x y : Ob} (f : x ⇒ y) -> f ∘ (id {x}) ≡ f
    idʳ : ∀ {x y : Ob} (f : x ⇒ y) -> (id {y}) ∘ f ≡ f
    ∘-assoc : ∀ {x y z w : Ob} (f : x ⇒ y) (g : y ⇒ z) (h : z ⇒ w) -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

Lens∘ : { S T A B C D : Set } → Lens S T A B → Lens A B C D → Lens S T C D
Lens∘ p q = p ∘ₚ q

Bimorphic : Category
Bimorphic = record
                { Ob = Set × Set
                ; _⇒_ = λ { (S , T) → λ { (A , B) → Lens S T A B} }
                ; _∘_ = λ { record { onPos = onPos ; onDir = onDir }  -- just _∘ₚ_ ....
                      → λ { record { onPos = onPos' ; onDir = onDir' } 
                      → record { onPos = λ x₁ → onPos (onPos' x₁)  ; onDir = λ i z → onDir' i (onDir (onPos' i) z) } } }
                ; id = record { onPos = λ z → z ; onDir = λ i z → z }
                ; idˡ = λ f₁ → refl
                ; idʳ = λ f₁ → refl
                ; ∘-assoc = λ f₁ g h → refl
                }
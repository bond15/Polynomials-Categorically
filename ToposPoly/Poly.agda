{-# OPTIONS --type-in-type #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Poly where 

open import Base 
open import Data.Unit
open import Agda.Builtin.Sigma 
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)

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

-- the 4 monoidal structures on Poly

_⊎ₚ_ : Poly → Poly → Poly
p ⊎ₚ q = record { pos = pos p ⊎ pos q ; dir = λ { (inj₁ x) → (dir p) x
                                                ; (inj₂ y) → (dir q) y } }

-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ
_×ₚ_ : Poly → Poly → Poly
p ×ₚ q = record { pos = pos p × pos q ; dir = λ {(i , j) → (dir p) i ⊎ (dir q) j} }

--tensor \ox
-- Ayᴮ × Cyᴰ = ACyᴮᴰ
_⊗ₚ_ : Poly → Poly → Poly
p ⊗ₚ q = record { pos = pos p × pos q ; dir = λ {(i , j) → (dir p) i × (dir q) j} }
-- show these are all monoidal structures on poly

-- composition of polynomials
-- notation suggests that p ◃ q, means that q is substituted into p
-- show that this is an example of composition of datatypes!

_◃_ : Poly → Poly → Poly
(p⑴ ▹ p[_] ) ◃ (q⑴ ▹ q[_]) = (Σ[ i ∈ p⑴ ] (p[ i ] → q⑴)) ▹ λ{ ( i , ĵ) → Σ[ d ∈ p[ i ] ]  q[ (ĵ d) ]}


record Polyₓ (p q : Poly) : Set where
    field
        posₓ : pos p × pos q
        dirₓ : (pq : pos p × pos q) → (dir p) (fst pq) ⊎ (dir q) (snd pq) 


record Poly[_,_](p q : Poly) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Poly[_,_]

-- RENAME 
_⇒∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ⇒∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) o ((onDir qr) ((onPos pq) i)) } -- backward composition on directions

-- Chart
-- forward on positions and forward on arrows
--https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- found DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf
record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square between the 4 polys

Poly[] : Poly → Poly → Set
Poly[] p q = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ∀ (d : dir q j) → Σ (dir p i) λ c → Unit )


lemma-poly[]-iso : {p q : Poly} → Poly[] p q ≈ Poly[ p , q ]
lemma-poly[]-iso {p} {q} = record { to = λ p[] → record { onPos = λ ppos → fst( p[] ppos) ; onDir = λ ppos x → fst(snd(p[] ppos) x) } 
                        ; from = λ poly[p,q] ppos → (onPos poly[p,q]) ppos , λ d → (onDir poly[p,q]) ppos d , unit 
                        ; from∘to = λ poly[]pq → Extensionality λ x → {! ? !}
                        ; to∘from = λ poly[p,q] → refl }

elem : Poly → Set
elem p = Σ (pos p) (dir p)


lift : {X Y : Set} → (p : Poly) → (X → Y) → (⦅ p ⦆ X → ⦅ p ⦆ Y)
lift p f = λ{ (fst₁ , snd₁) → fst₁ , snd₁ ؛ f}

yˢ : (S : Set) → Poly
yˢ S = Unit ▹ λ _ → S

𝓎 : Poly
𝓎 = Unit ▹ (λ _ → Unit)

yoneda : {S : Set} → {q : Poly} → Poly[ yˢ S , q ] ≈ ⦅ q ⦆ S
yoneda =  record { to = λ{ record { onPos = onPos ; onDir = onDir } → onPos unit , λ x → onDir unit x } 
                    ; from = λ { (fst₁ , snd₁) → record { onPos = λ _ → fst₁ ; onDir = λ i → snd₁ } } 
                    ; from∘to = λ{ record { onPos = onPos ; onDir = onDir } → {! refl  !} } 
                    ; to∘from = λ { (fst₁ , snd₁) → refl } }


-- Set^Vars → Set
-- or Set^I → Set
record Polyₘ (Vars : Set) : Set where
    constructor _▹ₘ_
    field
        Pos : Set
        Dir : Pos → ∀ (var : Vars) → Set

⦅_⦆⋆_ : {Vars : Set} → Polyₘ Vars → (Vars → Set) → Set 
(⦅_⦆⋆_) {Vars} (Pos ▹ₘ Dir) f = Σ[ p ∈ Pos ] (∀ (var : Vars) → (Dir p var → f var ))

-- https://www.youtube.com/watch?v=B8STLcbEGrE&list=PLhgq-BqyZ7i7R-fGcAmNyWmJBQg1wzex-&index=1
-- Richard Garner's talk
-- the even more general case is 
-- Set^I → Set^J 
-- "A J indexed family of polynomial functors Set^I → Set"
-- claim: this is better for composition ?

-- Alternatively functors Set/I → Set/J ??
-- slice category?

-- another representation ( I've seen this before in some papers..)
-- Set/I → Set/E → Set/B → Set/J

-- Also Girard's Normal Functors?


module ExampleMultivariate where
    open import Data.Bool
    open import Data.Nat

    -- set of variables
    data V : Set where
        X Y Z : V

    -- 3 variables X Y Z
    -- P(x,y,z) = (x^2)(z^3) + xz + 1
    mp : Polyₘ V
    mp = record { 
        Pos = Pos₃ ; 
        Dir = λ { P₁ X → Dir₂ -- x^2
                ; P₁ Y → Dir₀
                ; P₁ Z → Dir₃ -- z^3

                ; P₂ X → Dir₁ -- x
                ; P₂ Y → Dir₀
                ; P₂ Z → Dir₁ -- z

                ; P₃ X → Dir₀
                ; P₃ Y → Dir₀
                ; P₃ Z → Dir₀ }}

    assignVars : V → Set
    assignVars X = Bool
    assignVars Y = Unit
    assignVars Z = ℕ

    _ : ⦅ mp ⦆⋆ assignVars 
    _ = P₁ , λ{X D₁ → true
             ; X D₂ → false

             ; Z D₁ → 1
             ; Z D₂ → 2
             ; Z D₃ → 3}

-- PolyBoxes
module composition where
    p : Poly  
    p = Pos₂ ▹ (λ{P₁ → Dir₂
                ; P₂ → Dir₁})

    p' : Poly
    p' = Pos₂ ▹ λ{P₁ → Dir₃
                ; P₂ → Dir₁}

    q : Poly
    q = Pos₂ ▹ (λ{P₁ → Dir₂
                ; P₂ → Dir₁})

    q' : Poly
    q' = Pos₂ ▹ (λ{P₁ → Dir₁
                 ; P₂ → Dir₀})


    p→p' : Poly[ p , p' ]
    p→p' = (λ{P₁ → P₁
            ; P₂ → P₂}) ⇒ₚ λ{P₁ D₁ → D₂
                           ; P₁ D₂ → D₂
                           ; P₁ D₃ → D₁
                           ; P₂ D₁ → D₁}

    q→q' : Poly[ q , q' ]
    q→q' = (λ{P₁ → P₁
            ; P₂ → P₂}) ⇒ₚ λ{P₁ D₁ → D₂}

    _ : Poly[ p ◃ q , p' ◃ q' ]
    _ = {!   !}

    -- Sy^S is a contractible groupoid ??

    _◃→_ : {p p' q q' : Poly} → (f : Poly[ p , p' ]) → (g : Poly[ q , q' ]) → Poly[ p ◃ q , p' ◃ q' ]
    (onPos₁ ⇒ₚ onDir₁) ◃→ (onPos₂ ⇒ₚ onDir₂) = 
            (λ{ (posp , pdirtoq) → onPos₁ posp , λ{x → onPos₂ (pdirtoq (onDir₁ posp x))}}) 
            ⇒ₚ λ{(posp , snd₁) (fst₁ , snd₂) → (onDir₁ posp fst₁) , (onDir₂ (snd₁ (onDir₁ posp fst₁)) snd₂)}








-- failed attempts at trying to derive multivarite polynomials
-- multivariate polynomials?
-- data types with more that one type variable?
-- two variables
{-
module multivariate where
    ⦅_⦆[_,_] : Poly → Set → Set → (Pos₂ → Set)
    ⦅ P ▹ D ⦆[ S₁ , S₂ ] = λ{P₁ → Σ[ p ∈ P ] (D p → S₁)
                        ; P₂ → Σ[ p ∈ P ] (D p → S₂)}

    ⦅_⦆[_,_]' : Poly → Set → Set → ({Pos₂} → Set)
    ⦅ P ▹ D ⦆[ S₁ , S₂ ]' {P₁} = Σ[ p ∈ P ] (D p → S₁)
    ⦅ P ▹ D ⦆[ S₁ , S₂ ]' {P₂} = Σ[ p ∈ P ] (D p → S₂)

    multi : {I : Set} → Poly → (I → Set) → (i : I) → Set
    multi {I} (P ▹ D) f i = Σ[ p ∈ P ] (D p → f i)

    multi' : {I : Set} → Poly -> (I → Set) → Set
    multi' {I} (P ▹ D) f = (∀ (i : I) → Σ[ p ∈ P ] (D p → f i))

    multi'' : {I : Set} → Poly -> (I → Set) → Set
    multi'' {I} (P ▹ D) f = Σ[ p ∈ P ] (D p → (∀ (i : I) → f i))

    multi''' : {I : Set} → Poly -> (I → Set) → Set
    multi''' {I} (P ▹ D) f = Σ[ p ∈ P ] (D p → Σ[ i ∈ I ] f i)

    --multi' : {I : Set} → ((P ▹ D) : Poly) → (f : I → Set) → (∀ (i : I) → Σ[ p ∈ P ] (D p → f i))
   -- multi' {I} (P ▹ D) f i = {!   !} , {!   !}

    ⦅_⦆[_at_] : {I : Set} → Poly → (I → Set) → (i : I) → Set
    (⦅_⦆[_at_]) {I} (P ▹ D) f i = Σ[ p ∈ P ] (D p → f i)


    open import Data.Bool
    open import Data.Nat
    p : Poly
    p = Pos₂ ▹ λ{P₁ → Dir₂
                ; P₂ → Dir₀ }

    _ : ⦅ p ⦆[ ℕ , Bool ] P₁
    _ = P₁ , (λ{ D₁ → 7
            ; D₂ → 3})

    vars : Pos₃ → Set
    vars P₁ = ℕ
    vars P₂ = Dir₀
    vars P₃ = Bool

    -- this formulation is basically the univariate formulation
    -- with the indirection of f i = X
    _ : multi p vars P₃
    _ = P₁ , λ{ D₁ → true
            ; D₂ → false}
    _ : multi p vars P₁
    _ = P₁ , λ{ D₁ → 6
            ; D₂ → 3}       

    _ : ⦅ p ⦆[ vars at P₁ ]
    _ = P₁ , λ{ D₁ → 6
              ; D₂ → 3}  

    --arhg : {p : Pos₂} → ⦅ xp ⦆[ ℕ , Bool ]'
    --arhg {P₁} = P₁ ,  (λ{D₁ → {! 9  !}
    --           ; D₂ → {! 4  !} })    

    

    -- this formulation says
    -- for each variable, give me a polynomial...
    -- which is not quite right.. we want to allow for A polynomial to have many variables
    _ : multi' p vars
    _ = λ{P₁ → P₁ , (λ{ D₁ → 6
                      ; D₂ → 8})
        ; P₂ → P₂ , λ()
        ; P₃ → P₁ , (λ{D₁ → false
                     ; D₂ → true}) }

    -- this formulation delays the choice of type until a position and direction have been chosen
    -- but you select a value for each variable!
    -- instead you want to select just 1 value, soooo  Use a Sigma type instead!
    _ : multi'' p vars
    _ = P₁ , λ{D₁ → λ{P₁ → 6
                    ; P₂ → {!   !}
                    ; P₃ → false}
             ; D₂ → λ{P₁ → 7
                    ; P₂ → {!   !}
                    ; P₃ → true}}

    -- is this valid though...?
    _ : multi''' p vars
    _ = P₁ , λ{D₁ → P₁ , 7
             ; D₂ → P₃ , true}

    -- wait... why are you parameterizing the type with a univariate polynomial??



                

module Example where
    p : Poly
    p = Pos₁ ▹ λ{ P₁ → Dir₂ }

    open import Data.Bool
    _ : ⦅ p ⦆ Bool
    _ = P₁ , λ{D₁ → false
             ; D₂ → true}

    q : Poly
    q = Pos₂ ▹ (λ { P₁ → Dir₂
                  ; P₂ → Dir₁ })
    
    r : Poly
    r = Pos₂ ▹ (λ{ P₁ → Dir₃
                 ; P₂ → Dir₀ })

    _ : Poly[ p , q ◃ r ]
    _ = (λ{P₁ → P₁ , (λ{D₁ → P₁
                      ; D₂ → P₁})}) 
                      
        ⇒ₚ λ{P₁ (D₁ , D₁) → D₁
           ; P₁ (D₁ , D₂) → D₁
           ; P₁ (D₁ , D₃) → D₁
           ; P₁ (D₂ , D₁) → D₂
           ; P₁ (D₂ , D₂) → D₂
           ; P₁ (D₂ , D₃) → D₂}
-}
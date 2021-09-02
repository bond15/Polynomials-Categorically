{-# OPTIONS --copatterns #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --type-in-type #-}
module Dynamics where

open import Data.Product
open import Data.Nat
open import Data.List
-- Internal States S
-- Input alphabet I
-- Output alphabet O
record MooreMachine (I O S : Set) : Set where
    constructor M_,_
    field 
        return : S → O
        update : S × I → S
open MooreMachine
{- 
 Example - 
    A two state moore machine that has a Bool input alphabet and a ℕ output alphabet
    -- switch state whenever tt is seen
    -- stay in current state whenever ff is seen

    ff ^ (s1)  --tt ->  (s2) ^ ff
               <--tt--
-}

data State₂ : Set where
    S₁ S₂ : State₂

data Bool : Set where
    tt ff : Bool 

m₁ : MooreMachine Bool ℕ State₂
m₁ = record { 
    return = λ { S₁ → 4
               ; S₂ → 7} ; 
    update = λ { (S₁ , tt) → S₂
               ; (S₁ , ff) → S₁
               ; (S₂ , tt) → S₁
               ; (S₂ , ff) → S₂ } }

-- Stream semantics for MooreMachines

record Stream (X : Set) : Set where
    constructor _◂_
    coinductive
    field
        hd : X 
        tl : Stream X
open Stream          

seven : Stream ℕ
hd (seven) = 7
tl (seven) = seven

not : Bool → Bool
not tt = ff
not ff = tt

alt : Bool → Stream Bool
hd (alt b) = b
tl (alt b) = alt (not b)

Trace : {I O S : Set} → (M : MooreMachine I O S) → S → Stream I → Stream (I × S × O)
hd (Trace (M return , update) s is )= hd is , s , return s
tl (Trace (M return , update) s is) = Trace ((M return , update)) (update (s , hd is)) (tl is) 

stake : { X : Set } → Stream X → ℕ → List X
stake is zero = []
stake is (suc n) = hd is ∷ stake (tl is) n

m₁trace : Stream (Bool × State₂ × ℕ)
m₁trace = Trace m₁ S₁ (alt tt)

_ : List (Bool × State₂ × ℕ)
_ = stake m₁trace 7



-- Note the similarity to Lenses!
open import Poly
open import Lens
open import Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)



-- Syˢ → Ayᴮ
-- Lens S T A B = Poly[ S ▹ (λ _ →  T) , A ▹ (λ _ → B) ]
MM : (I O S : Set) → Set
MM I O S = Lens S S O I

Trace' : {I O S : Set} → (M : MM I O S) → S → Stream I → Stream (I × S × O)
hd (Trace' (onPos ⇒ₚ onDir) s is) = hd is , s , onPos s
tl (Trace' (onPos ⇒ₚ onDir) s is) = Trace' (onPos ⇒ₚ onDir) (onDir s (hd is)) (tl is) 

_ : {I O S : Set} → MM I O S ≈ MooreMachine I O S
_ = record { 
    to = λ{ (onPos ⇒ₚ onDir) → M onPos , λ (s , i) → onDir s i } ;
    from = λ{ (M return₁ , update₁) → return₁ ⇒ₚ λ s i → update₁ ( s , i )} ; 
    from∘to = λ x → refl ;
    to∘from = λ x → refl } 
-- so more machines are instances of Lenses or maps between monomials

-- Note that his should have the exact same stream semantics as m₁ : MoreMachine
m₂ : MM Bool ℕ State₂
m₂ = (λ { S₁ → 4
       ; S₂ → 7}) ⇒ₚ λ { S₁ tt → S₂
                       ; S₁ ff → S₁
                       ; S₂ tt → S₁
                       ; S₂ ff → S₂}
m₂trace : Stream (Bool × State₂ × ℕ)
m₂trace = Trace' m₂ S₁ (alt tt) 

_ : stake m₁trace 7 ≡ stake m₂trace 7
_ = refl


open import Data.Integer


-- Turing machine as a LensS

data Var : Set where
    One Zero Empty : Var

data HeadDir : Set where
    L R : HeadDir 


-- (Z → V × V)  ≈> the tape × current position
-- V -- output

TuringMachine : Set
TuringMachine = Lens ((ℤ → Var) × ℤ) ((ℤ → Var) × ℤ) Var ( Var × HeadDir)

eqℕ : ℕ → ℕ → Bool
eqℕ zero zero = tt
eqℕ zero (ℕ.suc m) = ff
eqℕ (ℕ.suc n) zero = ff
eqℕ (ℕ.suc n) (ℕ.suc m) = eqℕ n m

eqℤ : ℤ → ℤ → Bool
eqℤ (+_ n) (+_ n₁) = eqℕ n n₁
eqℤ (+_ n) (-[1+_] n₁) = ff
eqℤ (-[1+_] n) (+_ n₁) = ff
eqℤ (-[1+_] n) (-[1+_] n₁) = eqℕ n n₁

if_then_else_ : {A : Set} → Bool → A → A → A 
if tt then e₁ else e₂ = e₁
if ff then e₁ else e₂ = e₂

_[_⇒_] : {B : Set} → (ℤ → B) → ℤ → B → (ℤ → B)
f [ x ⇒ v ] = λ x' → if eqℤ x x' then v else f x'

_ : TuringMachine
_ = (λ {(tape , head) → tape(head)}) ⇒ₚ λ{ (tape , head) ( v , L) → (tape [ head ⇒ v ]) , head - (+_ 1)
                                         ; (tape , head) ( v , R) → (tape [ head ⇒ v ]) , Data.Integer._+_ head (+_ 1) }


{- Dependent Dynamical Systems

    So far we have only looked at systems where the "interface" is a monomial Byᴬ 
    Syˢ → Byᴬ

    
-}
open Poly.Poly
open import Data.Sum.Base

-- Syˢ → ℕy^ℕ + Booly^Bool
Ex : Set → Set
Ex S = Poly[ S ▹ (λ _ → S) , (ℕ ▹ λ _ → ℕ) ⊎ₚ (Bool ▹ λ _ → Bool) ]

{-
 P₁ 7
 P₂ True
 p₃ 14
 p₄ False

-}
-- states can read off different types
-- states can transition on different types
_ : Ex Pos₄ 
_ = (λ {P₁ → inj₁ 7
      ; P₂ → inj₂ tt
      ; P₃ → inj₁ 14
      ; P₄ → inj₂ ff}) ⇒ₚ λ { P₁ → λ n → P₂
                            ; P₂ → λ b → P₃
                            ; P₃ → λ n → P₄
                            ; P₄ → λ b → P₁}

-- Haulting deterministic state automata
data Nada : Set where
-- Syˢ → yᴬ + 1
HDSA : Set → Set → Set
HDSA S A = Poly[ S ▹ (λ _ → S) , (Unit ▹ λ _ → A) ⊎ₚ (Unit ▹ λ _ → Nada) ]                         


-- P₁ -tt-> P₂ -ff-> P₃
-- p₄ is trash state
-- accept the language ttff(ttff)*
-- NOPE
-- this representation doesn't follow the language acceptance model...
-- an accept state does not terminate.. you only terminate once input has been exhausted..
_ : HDSA Pos₄ Bool
_ = (λ {P₁ → inj₁ unit
      ; P₂ → inj₁ unit
      ; P₃ → inj₂ unit
      ; P₄ → inj₁ unit }) ⇒ₚ λ{ P₁ → λ{ tt → P₂
                                      ; ff → P₄ }
                             ; P₂ → λ {tt → P₄
                                     ; ff → P₃}
                             ; P₃ → λ () -- problem.. this haults the machine.. there could be more input
                             ; P₄ → λ _ → P₄}

record Graph : Set where
    field
        V : Set
        E : Set
        source : E → V
        target : E → V
open Graph
-- graph representing the above state machine
graph : Graph
graph = record { 
    V = Pos₄ ;
    E = Pos₄ × Bool ;
    source = λ{(p , b) → p} ;
    target = λ{(P₁ , tt) → P₂
             ; (P₁ , ff) → P₄
             ; (P₂ , tt) → P₄
             ; (P₂ , ff) → P₃
             ; (P₃ , b) → P₃
             ; (P₄ , b) → P₄ } 
    }

fiber : {E B : Set} -> (f : E -> B) -> (b : B) -> Set
fiber {E} {B} f b = Σ E (λ e -> (f e ≡ b))

G : Graph → Poly
G g = V g ▹ λ v → fiber (source g) v

ex : Graph → Set
ex g = Poly[ V g ▹ (λ _ → V g) , G g ]

_ : ex graph
_ = (λ v → v) ⇒ₚ λ { _ (e , _) → target graph e}


-- Example 3.32
module Ex_3,32 where
{-
    record Sys (S : Set) : Set where
        constructor Syˢ⇒_
        field
            interface : Poly
    open Sys

    _×ₛ_ : {S : Set} → Sys S → Sys S → Sys S
    (Syˢ⇒ p) ×ₛ (Syˢ⇒ q) = Syˢ⇒ (p ×ₚ q)

    ⦅_⦆ₛ : {S : Set} → Sys S → Set
    ⦅_⦆ₛ {S} (Syˢ⇒ p) = Poly[ S ▹ (λ _ → S) , p ]
-}
    record Sys(S : Set)(p : Poly): Set where
        constructor Syˢ⇒_
        field
            system : Poly[ S ▹ (λ _ → S) , p ]
    open Sys

    open Poly[_,_]
    _×ₛ_ : {S : Set}{p q : Poly} → Sys S p → Sys S q → Sys S (p ×ₚ q)
    (Syˢ⇒ p) ×ₛ (Syˢ⇒ q) = Syˢ⇒ ((λ s → onPos p s , onPos q s) ⇒ₚ λ {i (inj₁ x) → onDir p i x
                                                                   ; i (inj₂ y) → onDir q i y})

    data RB : Set where
        red blue : RB

    data GP : Set where
        green purple : GP

    data Gr : Set where
        green : Gr
    
    data A : Set where
        A₁ A₂ A₃ A₄ : A
    
    data B : Set where
        B₁ B₂ B₃  B₄ : B



{-
    p1   p2
    
    p3   p4
-}
    I₁ : Poly
    I₁ = A ▹ (λ _ → RB)

    ϕ : Sys Pos₄ I₁
    ϕ = Syˢ⇒ ((λ{ P₁ → A₁
                ; P₂ → A₂
                ; P₃ → A₃
                ; P₄ → A₄ }) ⇒ₚ λ{ P₁ red → P₂
                                 ; P₁ blue → P₁
                                 ; P₂ red → P₁
                                 ; P₂ blue → P₄
                                 ; P₃ red → P₁
                                 ; P₃ blue → P₄
                                 ; P₄ red → P₃
                                 ; P₄ blue → P₄} )
{-
    p1  p2

    p3  p4

-}
    I₂ : Poly
    I₂ = (B ▹ (λ _ → GP)) ⊎ₚ (B ▹ (λ _ → Gr)) 

    ψ : Sys Pos₄ I₂
    ψ = Syˢ⇒ ((λ{ P₁ → inj₂ B₁
                ; P₂ → inj₁ B₂
                ; P₃ → inj₂ B₃
                ; P₄ → inj₁ B₄}) ⇒ₚ λ{ P₁ green → P₃
                                     ; P₂ green → P₁
                                     ; P₂ purple → P₄
                                     ; P₃ green → P₃
                                     ; P₄ green → P₁
                                     ; P₄ purple → P₃})

    {-
        syˢ → Ay^RB
        syˢ → By^GP + By^Gr

        to

        syˢ → (Ay^RB) × (By^GP + By^Gr)

        recall

        Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ

        so 

        syˢ → A(B+B)y^(RB + (GP + Gr ))
    -}

    exx : Sys Pos₄ (I₁ ×ₚ I₂)
    exx = ϕ ×ₛ ψ

    getp : {p q : Poly} → Poly[ p , q ] → Poly
    getp {p} {q} = λ _ → q

    geti : {S : Set} {p : Poly} → Sys S p → Poly
    geti = λ { (Syˢ⇒ system₁) → getp system₁ }

    _ : {O S : Set} → {I : O → Set} → (sys : Sys S (O ▹ (λ x → I x)) ) → Poly
    _ = geti

    -- observe a trace of this system
    --SysTrace : {O S : Set} → {I : O → Set} → {o : O} → (sys : Sys S (O ▹ (λ x → I x)) ) → ∀(s : S) →  Stream (I {! dir (geti sys) o !}) → Stream (I o × S × O)
   -- hd (SysTrace (Syˢ⇒ p) s is ) = hd is , s , onPos p s
    --tl (SysTrace (Syˢ⇒ p) s is ) = SysTrace (Syˢ⇒ p) (onDir p s (hd {! is   !})) (tl is)

    -- observe the output of the new system 
    -- the states are the same
    -- both outputs respect the original systems' outputs on state P₁
    _ : onPos (system exx) P₁ ≡ (A₁ , inj₂ B₁)
    _ = refl

    -- observe that transitions respect the original system
    _ : onDir (system exx) P₁ (inj₁ red) ≡ P₂
    _ = refl
    _ : onDir (system exx) P₁ (inj₁ blue) ≡ P₁
    _ = refl
    _ : onDir (system exx) P₁ (inj₂ green) ≡ P₃
    _ = refl
    -- no purple arrows going out of state P₁
    
    _ : I₁ ×ₚ I₂ ≡ ( (A × (B ⊎ B)) ▹ λ{ (a , bub) → dir I₁ a ⊎ dir I₂ bub })
    _ = refl

    _ : Sys Pos₄ (( (A × (B ⊎ B)) ▹ λ{ (a , bub) → dir I₁ a ⊎ dir I₂ bub }))
    _ = exx



    -- Parallel Product of systems
    -- note states need not be the same 

    _⊗ₛ_ : {S₁ S₂ : Set} {p q : Poly} → Sys S₁ p → Sys S₂ q → Sys (S₁ × S₂) (p ⊗ₚ q) 
    sys₁ ⊗ₛ sys₂ = Syˢ⇒ ((λ {(s₁ , s₂) → onPos (system sys₁) s₁ , onPos (system sys₂) s₂}) ⇒ₚ λ { (s₁ , s₂) (o₁ , o₂) → onDir (system sys₁) s₁ o₁ , onDir (system sys₂) s₂ o₂})

    -- example 3.35

    data RO : Set where
        red orange : RO
    data Bl : Set where
        blue : Bl
    data Red : Set where
        red : Red
    data Or : Set where
        orange : Or
    
    open import Data.String

    I₃ : Poly
    I₃ = (String ▹ λ _ → Bl) ⊎ₚ (String ▹ λ _ → RB)

    I₄ : Poly
    I₄ = ((String ▹ λ _ → Red) ⊎ₚ (String ▹ λ _ → RO)) ⊎ₚ (String ▹ λ _ → Or)

    ϕ₂ : Sys Pos₂ I₃
    ϕ₂ = Syˢ⇒ ((λ { P₁ → inj₁ "sqrt(7)"
                  ; P₂ → inj₂ "-e" }) ⇒ₚ λ {P₁ blue → P₂
                                          ; P₂ red → P₁
                                          ; P₂ blue → P₂})

    ψ₂ : Sys Pos₃ I₄
    ψ₂ = Syˢ⇒ ((λ {P₁ → inj₁ (inj₁  "-5")
                 ; P₂ → inj₁  (inj₂ "0")
                 ; P₃ → inj₂ "8"}) ⇒ₚ λ { P₁ red → P₂
                                        ; P₂ red → P₃
                                        ; P₂ orange → P₁
                                        ; P₃ orange → P₃})


    -- observe their parallel product
    ex₂ : Sys (Pos₂ × Pos₃) (I₃ ⊗ₚ I₄)
    ex₂ = ϕ₂ ⊗ₛ ψ₂

    -- top left corner state
    _ : onPos (system ex₂) (P₁ , P₁) ≡ (inj₁ "sqrt(7)" , inj₁ (inj₁ "-5"))
    _ = refl

    -- bimap?
    _ : onDir (system ex₂ ) (P₁ , P₁) (blue , red) ≡ (P₂ , P₂)
    _ = refl
    
    _ : onDir (system ex₂) (P₂ , P₃) (blue , orange) ≡ (P₂ , P₃)
    _ = refl


    -- Wrapper Interfaces

    _∘ₛ_ : {S : Set} {p q : Poly} → Sys S p → Poly[ p , q ] → Sys S q
    (Syˢ⇒ f) ∘ₛ g = Syˢ⇒ (f ∘ₚ g)

    data BYR : Set where
        blue yellow red : BYR
    -- example 3.38
    I₅ : Poly
    I₅ =  (String ▹ (λ _ → BYR)) ⊎ₚ  ((String ▹ (λ _ → RB)) ⊎ₚ  ((String ▹ λ _ → Bl) ⊎ₚ  (String ▹ λ _ → Red))) 

    data Pos₆ : Set where
        P₁ P₂ P₃ P₄ P₅ P₆ : Pos₆


    -- p1 p2 p3
    ---p4 p5 p6
    ϕ₃ : Sys Pos₆ I₅ 
    ϕ₃ = Syˢ⇒ ((λ {P₁ → inj₁ "1"
                 ; P₂ → inj₂ (inj₁  "2")
                 ; P₃ → inj₂ (inj₂ (inj₁ "3"))
                 ; P₄ → inj₂ (inj₂  (inj₂ "4"))
                 ; P₅ → inj₁ "1" -- ?????
                 ; P₆ → inj₂ (inj₂  (inj₂ "4"))}) ⇒ₚ λ{ P₁ blue → P₂
                                          ; P₁ yellow → P₅
                                          ; P₁ red → P₄
                                          ; P₂ red → P₅
                                          ; P₂ blue → P₂
                                          ; P₃ blue → P₂
                                          ; P₄ red → P₄
                                          ; P₅ blue → P₄
                                          ; P₅ yellow → P₂
                                          ; P₅ red → P₆
                                          ; P₆ red → P₃})
    data GPO : Set where
        green purple orange : GPO

    data None : Set where

    qpoly : Poly
    qpoly = (String ▹ (λ _ → GPO))  ⊎ₚ ((String ▹ (λ _ → GP))  ⊎ₚ (String ▹ (λ _ → None )))

    f : Poly[ I₅ , qpoly ]
    f = (λ {(inj₁ x) → inj₂ (inj₁ "b") -- 1 to b
          ; (inj₂ (inj₁ x)) → inj₂ (inj₂  "c") -- 2 to c
          ; (inj₂ (inj₂ (inj₁ x))) → inj₂ (inj₁ "b") -- 3 to b
          ; (inj₂ (inj₂ (inj₂ y))) → inj₁ "a"}) -- 4 to a
            ⇒ₚ λ {(inj₁ x₁) green → red -- arrows b to 1
                ; (inj₁ x₁) purple → yellow
                ; (inj₂ (inj₂ (inj₁ x₁))) green → blue -- arrows b to 3
                ; (inj₂ (inj₂ (inj₁ x₁))) purple → blue
                ; (inj₂ (inj₂ (inj₂ y))) green → red -- arrows a to 4
                ; (inj₂ (inj₂ (inj₂ y))) purple → red
                ; (inj₂ (inj₂ (inj₂ y))) orange → red} 

    -- wrapper example
    ν : Sys Pos₆ qpoly
    ν = ϕ₃ ∘ₛ f

    -- Think. re-lable the output states, then re map directions

    _ : onPos (system ν) P₁  ≡ inj₂ (inj₁ "b")
    _ = refl

    _ : onDir (system ν) P₁ purple ≡ P₅
    _ = refl
    _ : onDir (system ν) P₁ green ≡ P₄
    _ = refl

    _ : None → Pos₆
    _ = onDir (system ν) P₂


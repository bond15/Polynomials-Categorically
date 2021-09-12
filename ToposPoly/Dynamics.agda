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


open import Data.Integer hiding (_+_)


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
tfsys : HDSA Pos₄ Bool
tfsys = (λ {P₁ → inj₁ unit
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
tfsys_graph : Graph
tfsys_graph = record { 
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

Gₚ : Graph → Poly
Gₚ g = V g ▹ λ v → fiber (source g) v


-- Example 3.32
module Systems where
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
    open Poly[_,_]

    record Sys(S : Set)(p : Poly): Set where
        constructor Syˢ⇒_
        field
            system : Poly[ S ▹ (λ _ → S) , p ]
    open Sys
    
    GSyˢ : (g : Graph) → Sys (V g) (Gₚ g)
    GSyˢ graph = Syˢ⇒ ((λ v → v) ⇒ₚ λ { _ ( e , _) → target graph e})

    _ : (onDir (system (GSyˢ tfsys_graph))) P₂ ((P₂ , ff) , refl) ≡ P₃
    _ = refl


    _×ₛ_ : {S : Set}{p q : Poly} → Sys S p → Sys S q → Sys S (p ×ₚ q)
    (Syˢ⇒ p) ×ₛ (Syˢ⇒ q) = Syˢ⇒ ((λ s → onPos p s , onPos q s) ⇒ₚ λ {i (inj₁ x) → onDir p i x
                                                                   ; i (inj₂ y) → onDir q i y})

    data RB : Set where
        red blue : RB

    data GP : Set where
        green purple : GP

    data Gr : Set where
        green : Gr
    
    data Aₜ : Set where
        A₁ A₂ A₃ A₄ : Aₜ
    
    data Bₜ : Set where
        B₁ B₂ B₃  B₄ : Bₜ



{-
    p1   p2
    
    p3   p4
-}
    I₁ : Poly
    I₁ = Aₜ ▹ (λ _ → RB)

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
    I₂ = (Bₜ ▹ (λ _ → GP)) ⊎ₚ (Bₜ ▹ (λ _ → Gr)) 

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
    
    _ : I₁ ×ₚ I₂ ≡ ( (Aₜ × (Bₜ ⊎ Bₜ)) ▹ λ{ (a , bub) → dir I₁ a ⊎ dir I₂ bub })
    _ = refl

    _ : Sys Pos₄ (( (Aₜ × (Bₜ ⊎ Bₜ)) ▹ λ{ (a , bub) → dir I₁ a ⊎ dir I₂ bub }))
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
    (Syˢ⇒ f) ∘ₛ g = Syˢ⇒ (f ⇒∘ₚ g)

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


    -- Add a pause button to a dynamical system
    -- Syˢ → By^A  ==>   Syˢ → By^(A+1)
    -- Byᴬ xₚ y  ==> By^(A+1)
    -- \Mcy
    addPause : ∀ {S : Set}{p : Poly} → Sys S p → Sys S (p ×ₚ 𝓎)
    addPause {S} {p} (Syˢ⇒ (onP ⇒ₚ onD)) = Syˢ⇒ ((λ s → onP s , unit) ⇒ₚ λ{ s (inj₁ x) → onD s x
                                                                          ; s (inj₂ unit) → s })

    -- alternatively
    pauseSyˢ : ∀ {S : Set} → Sys S 𝓎
    pauseSyˢ = Syˢ⇒ ((λ _ → unit) ⇒ₚ λ s unit → s)       

    addPause' : ∀ {S : Set}{p : Poly} → Sys S p → Sys S (p ×ₚ 𝓎)
    addPause' sys = sys ×ₛ pauseSyˢ                                                            


module WiringDiagrams where
    open Systems

    postulate A B C D S T : Set

    -- component boxes
    -- By^(AC)
    -- and
    -- CDy^B
    p : Poly
    p = B ▹ λ _ → A × C
    
    q : Poly
    q = (C × D) ▹ λ _ → B

    -- encapsulating box
    -- Dy^A
    r : Poly
    r = D ▹ λ _ → A

    -- select the component boxes
    p⊗q : Poly
    p⊗q = p ⊗ₚ q 

    -- define a wrapper interface from the inner box to the encapsulating box
    box :  Poly[ p⊗q , r ]
    box = (λ{ (b , c , d) → d}) -- outputs of separate boxes → output of enclosing box
        ⇒ₚ λ{ (b , c , _) a → (a , c) , b} -- input of enclosing box `a`, feed `b` and `c` back in


    -- "fill in the system"

    postulate part₁ : Sys S p -- assume an implementation of a system for p box
    postulate part₂ : Sys T q -- assume an implementation of a system for q box

    parts : Sys (S × T) (p ⊗ₚ q ) -- tensor the implementations together
    parts = part₁ ⊗ₛ part₂        -- they are in parallel and they do not interact

    -- "derives" an implementation of the encapsulating system
    -- given
    -- * implementations for the sub components
    -- * a formula for tying the boxes together
    newSys : Sys (S × T) r 
    newSys = parts ∘ₛ box

    open Systems
    open Sys
    open Poly[_,_]
    postulate s : S
    postulate t : T
    postulate d : D
    postulate a : A
    postulate n : None
    exfalso : {A : Set} → None → A
    exfalso()

    -- this shows that output of the new system is D
    _ : onPos (system newSys) (s , t) ≡ d
    _ = exfalso n

    -- this shows that input of the new system is A
    _ : onDir (system newSys) (s , t) a ≡ (s , t)
    _ = exfalso n

module testing where


module WiringDiagramsConcrete where
    open Systems
    open Sys
    open Poly[_,_]

    xorTy : Poly
    xorTy = Bool ▹ λ _ → Bool × Bool
    
    dupTy : Poly
    dupTy = (Bool × Bool) ▹ λ _ → Bool

    circuit : Poly
    circuit = (Bool ▹ λ _ → Bool)

    ten : Poly
    ten = xorTy ⊗ₚ dupTy

    box :  Poly[ ten , circuit ]
    box = (λ{ (b , c , d) → d}) 
        ⇒ₚ λ{ (b , c , _) a → (a , c) , b}


    xor : Sys Bool xorTy
    xor = Syˢ⇒ ((λ x → x) ⇒ₚ λ{ _ (tt , tt) → ff
                                ; _ (tt , ff) → tt
                                ; _ (ff , tt) → tt
                                ; _ (ff , ff) → ff })

    dup : Sys (Bool × Bool) dupTy
    dup = Syˢ⇒ ((λ x → x) ⇒ₚ λ _ x → (x , x))

    parts : Sys (Bool × Bool × Bool) (xorTy ⊗ₚ dupTy)
    parts = xor ⊗ₛ dup   

    fun :  Sys (Bool × Bool × Bool) circuit
    fun = parts ∘ₛ box 

    -- So by wrapping the circuit in box, the interface changed from
    -- Bool × Bool × Bool as input to Bool × Unit as input
    -- The abstraction is a bit leaky and not a full black box as 
    -- the State is accumulated when components are tensored and 
    -- the state is not hidden from the boxed interface..
    _ : onPos (system fun) (tt , (tt , tt))  ≡ tt
    _ = refl


-- page 89
module EnclosureInterface where
    open Systems
    open import Data.Nat using (_+_)
    open Poly[_,_]
    open Systems.Sys

    closeSys : {S : Set} {p : Poly} → Sys S p → Poly[ p , 𝓎 ] → Sys S 𝓎
    closeSys = _∘ₛ_ 

    -- example system 
    -- state , ℕ 
    -- input : ℕ
    -- output : Bool
    -- Description: takes an input n : ℕ  and outputs if n + s is even or odd
    I : Poly
    I = Bool ▹ (λ _ → ℕ)

    even : ℕ → Bool
    even zero = tt
    even (suc zero) = ff
    even (suc (suc n)) = even n

    -- view : ℕ → Bool
    -- update : ℕ × ℕ → ℕ
    evenSys : Sys ℕ I 
    evenSys = Syˢ⇒ ( even  ⇒ₚ _+_ )

    _ : onPos (system evenSys) 7 ≡ ff
    _ = refl

    _ : onDir (system evenSys) 3 7 ≡ 10
    _ = refl

    closed : Sys ℕ 𝓎  -- have to select a (next?)state? (here 7). is it always in that state?
    closed = closeSys evenSys ((λ (_ : Bool) → unit) ⇒ₚ λ (_ : Bool) unit → 7)

    -- the close machine can only ever read out `unit`
    _ : ∀ {n : ℕ} → onPos (system closed) n ≡ unit
    _ = refl

    -- the close machine can only ever take in 'unit'
    _ : ∀ {n : ℕ} → onDir (system closed) n unit ≡ n + 7
    _ = refl

    -- It seems like this freezes the system in time?
    -- It is odd that this hides the inputs and outputs.. but the internal state is still exposed..?

module BitAnd where
    open Systems
    open Poly[_,_]
    open Systems.Sys
     --  Idea, take 4 independent one bit ands and yield a new and

    -- these are stateless so.. Unit? 
    -- no... we need to use the state to hold the output? wtf

    data 4Word : Set where
        word : Bool × Bool × Bool × Bool → 4Word

    andBitI : Poly
    andBitI = Bool ▹ λ _ → Bool × Bool

    _&_ : Bool → Bool → Bool
    tt & tt = tt
    _ & _ = ff

    _||_ : Bool → Bool → Bool
    ff || ff = ff
    _ || _ = tt

    --_&&_ : 4Word → 4Word → 4Word
    --word (b₁ , b₂ , b₃ , b₄) && word (b₅ , b₆ , b₇ , b₈) = word ((b₁ & b₅) , ((b₂ & b₆) , ((b₃ & b₇) , (b₄ & b₈))))

    bitAnder : Sys Bool andBitI
    bitAnder = Syˢ⇒ ((λ (b : Bool) → b) ⇒ₚ λ { _ (b₁ , b₂) → b₁ & b₂})

    glue : Sys (Bool × Bool × Bool × Bool) (andBitI ⊗ₚ (andBitI ⊗ₚ (andBitI ⊗ₚ andBitI)) )
    glue = bitAnder ⊗ₛ (bitAnder ⊗ₛ (bitAnder ⊗ₛ bitAnder))

    4I : Poly
    4I = 4Word ▹ (λ _ → 4Word × 4Word) 

    box : Poly[ (andBitI ⊗ₚ (andBitI ⊗ₚ (andBitI ⊗ₚ andBitI)) ) , 4I ]
    box = word ⇒ₚ (λ{ _ (word (b₁ , b₂ , b₃ , b₄) , word (b₅ , b₆ , b₇ , b₈)) → (b₁ , b₅) , (b₂ , b₆) , (b₃ , b₇) , b₄ , b₈})

    wordAnd : Sys (Bool × Bool × Bool × Bool) 4I
    wordAnd = glue ∘ₛ box

    _ : onPos (system wordAnd) (tt , (ff , (tt , ff))) ≡ word (tt , (ff , (tt , ff)))
    _ = refl

    _ : {i : Bool × Bool × Bool × Bool} → onDir (system wordAnd) i ((word ((tt , (ff , (tt , ff))))) , (word ((ff , (tt , (ff , tt)))))) ≡ (ff , ff , (ff , ff))
    _ = refl

    _ : {i : Bool × Bool × Bool × Bool} → 
                onPos (system wordAnd) 
                    (onDir (system wordAnd) i 
                        ((word ((tt , (ff , (tt , ff))))) , 
                         (word ((ff , (tt , (ff , tt))))))) ≡ word (ff , ff , (ff , ff))
    _ = refl

    compute : {i : Bool × Bool × Bool × Bool} → 4Word → 4Word → 4Word
    compute {i} x y = onPos (system wordAnd) (onDir (system wordAnd) i (x , y))


    five : 4Word
    five = word (ff , (tt , (ff , tt)))

    four : 4Word
    four = word (ff , (tt , (ff , ff)))

    _ : {i : Bool × Bool × Bool × Bool} → compute {i} five four ≡ four
    _ = refl

    -- We can reuse these definitions and just swap out the implementation of the parts
    2bitOp : Poly
    2bitOp = Bool ▹ λ _ → Bool × Bool

    4wordOp : Poly
    4wordOp = 4Word ▹ (λ _ → 4Word × 4Word)

    liftOp : (Bool → Bool → Bool) → Sys Bool 2bitOp
    liftOp f = Syˢ⇒ ((λ (b : Bool) → b) ⇒ₚ λ { _ (b₁ , b₂) → f b₁ b₂ })

    bitsToWord : Poly[ (2bitOp ⊗ₚ (2bitOp ⊗ₚ (2bitOp ⊗ₚ 2bitOp)) ) , 4wordOp ]
    bitsToWord = word ⇒ₚ 
                (λ{ _ (word (b₁ , b₂ , b₃ , b₄) , 
                       word (b₅ , b₆ , b₇ , b₈)) 
                        → (b₁ , b₅) , (b₂ , b₆) , (b₃ , b₇) , b₄ , b₈})

    wordSys : (op : Sys Bool 2bitOp) → Sys (Bool × Bool × Bool × Bool) 4wordOp
    wordSys op = (op ⊗ₛ (op ⊗ₛ (op ⊗ₛ op))) ∘ₛ bitsToWord

 
    OrWord : Sys (Bool × Bool × Bool × Bool) 4wordOp
    OrWord = wordSys (liftOp _||_)

    AndWord : Sys (Bool × Bool × Bool × Bool) 4wordOp
    AndWord = wordSys (liftOp _&_ )
    
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






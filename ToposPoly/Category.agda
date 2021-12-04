{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Category where 
open import Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)

REL : Set -> Set  -> Set 
REL A B = A -> B -> Set 

Rel :  Set -> Set 
Rel A  = REL A A 

-- Precategory (need to parameterize with equality)
record Category : Set where
  field
    Ob : Set 
    _⇒_ : Rel Ob
    _≋_ : ∀{A B : Ob} → Rel (A ⇒ B) 
    _∘_  : ∀ {x y z : Ob} -> y ⇒ z -> x ⇒ y -> x ⇒ z
    id : ∀ {o : Ob} -> o ⇒ o
    idˡ : ∀ {x y : Ob} (f : x ⇒ y) -> f ∘ (id {x}) ≡ f
    idʳ : ∀ {x y : Ob} (f : x ⇒ y) -> (id {y}) ∘ f ≡ f
    ∘-assoc : ∀ {x y z w : Ob} (f : x ⇒ y) (g : y ⇒ z) (h : z ⇒ w) -> h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f


-- \Mc<letter>
record Functor (𝒞 𝒟 : Category) : Set where
    private 
        module C = Category 𝒞
        module D = Category 𝒟
    field
        F₀ : C.Ob -> D.Ob
        F₁ : ∀ {A B} (f : C._⇒_ A B ) -> D._⇒_ (F₀ A) (F₀ B)

        identity : ∀ {A} -> (F₁ (C.id {A})) ≡ D.id {(F₀ A)}
        homomorphism : ∀ {A B C} -> (f : C._⇒_ A B) -> (g : C._⇒_ B C) ->
            F₁ (C._∘_ g f) ≡ D._∘_ (F₁ g) (F₁ f)

Agda : Category
Agda = record
        { Ob = Set
        ; _⇒_ = λ x y → (x → y)
        ; _≋_ = λ {A} → λ f g → ∀ (a : A) → f a ≡ g a
        ; _∘_ = _o_
        ; id = λ x → x
        ; idˡ = λ f → refl
        ; idʳ = λ f → refl
        ; ∘-assoc = λ f g h → refl 
        }


data Option (A : Set) : Set where
     None : Option A 
     Some : A → Option A

fmap : {A B : Set} → (f : A → B) → Option A → Option B 
fmap f None = None
fmap f (Some a) = Some (f a)

OptFun : Functor Agda Agda
OptFun = record { 
    F₀ = Option ; 
    F₁ = fmap ; 
    identity = extensionality λ{ None → refl
                               ; (Some x) → refl } ; 
    homomorphism = λ f g → extensionality λ{ None → refl
                                           ; (Some x) → refl } }

open import Data.List

id : {A : Set} → A → A
id a = a

lemma-map : {A : Set} → (xs : List A) → map id xs ≡ xs
lemma-map [] = refl
lemma-map (x ∷ xs) = cong₂ _∷_ refl (lemma-map xs) 

lemma-map-fusion : {A B C : Set} → (xs : List A) → (f : A → B) → (g : B → C) → map (g o f) xs ≡ ((map g) o (map f)) xs
lemma-map-fusion [] f g = refl
lemma-map-fusion (x ∷ xs) f g = cong₂ _∷_ refl  (lemma-map-fusion xs f g)

ListFun : Functor Agda Agda
ListFun = record { 
    F₀ = List ; 
    F₁ = map ; 
    identity = λ{a} → extensionality λ xs → lemma-map xs ;
    homomorphism = λ f g → extensionality λ x → lemma-map-fusion x f g }



{-
    F : C → D
    G : C → D

    X  =η=>  F (X) → G(X)

    X --f--> Y  ==>   F(X) --fmapf--> F(Y)
                        |               |
                        η X           η Y
                        |               |
                      G(X) --fmapf--> G(Y)
-}
record NatTrans {C D : Category } (ℱ 𝒢 : Functor C D) : Set where
    private
        module F = Functor ℱ
        module G = Functor 𝒢
    open F using (F₀ ; F₁)
    open Category C renaming (_⇒_ to _⇒C_)
    open Category D renaming (_⇒_ to _⇒D_; _∘_ to _∘D_; _≋_ to _≋D_)
    field
        η : ∀ X → F.F₀ X ⇒D G.F₀ X
        commute : ∀ {X Y}(f : X ⇒C Y) → ((η Y) ∘D (F₁ f)) ≋D (((G.F₁ f) ∘D η X))

-- natural transformations are polynomial functions
fun : {X : Set} → Option X → List X
fun None = []
fun (Some x) = [ x ]

open Category
open Functor
open NatTrans

_ : NatTrans OptFun ListFun
_ = record { 
    η = λ X → fun ;
    commute = λ { f None → refl
                ; f (Some x) → refl } }


{-
Category : Agda

Objects: Sets
Morphisms: Functions

Polynomial Functor

    P ≡ Σ Set (λ S → S → Set)

-}
open import Data.Product
{- Poly' : Set
Poly' =  Σ[ S ∈ Set ] (S → Set)

P : Set → Set
P X = Σ[ S ∈ Set ] (S → Set → X)

lift : {A B : Set} → (f : A → B) → P A → P B
lift f = λ {(pos , dira) → pos , λ pose set → f (dira pose pos)}
-}

-- 2.3.2 & 2.3.4
open import Poly
open Poly[_,_] 

-- This shows that Poly represents a polynomial functor (but note Poly is a Set!)
PFun : Poly → Functor Agda Agda -- application of yoneda?
PFun p = record { 
    F₀ = ⦅ p ⦆ ; 
    F₁ = lift p ; 
    identity = refl ; 
    homomorphism = λ f g → refl }
{-
need the "yoneda ed" form of this 
Poly[_,_] 
morphisms between poly 

This represents that Poly[_,_] (which is a map/function between Poly) represents a Natural transformation of polynomial functors
-}
PNat : {p q : Poly } → Poly[ p , q ] → NatTrans (PFun p) (PFun q)
PNat (onPos ⇒ₚ onDir) = record { 
                            η = λ ob → λ{ (posp , dirp) → onPos posp , λ z → dirp (onDir posp z) } ; 
                            commute = λ {f (fst , snd) → refl }
                            }


-- Apply this yonedaificaton to Option : Functor Agda Agda and List : Functor Agda Agda

-- show that Option as a Functor Agda Agda is isomorphic to ⦅ Option' ⦆ as a Poly
Option' : Poly
Option' = Pos₂ ▹ λ { P₁ → Dir₁
                   ; P₂ → Dir₀ }
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


lemma-dumber : (x : Dir₁) → x ≡ D₁
lemma-dumber D₁ = refl

lemma-dumb : { X : Set } → ( f : Dir₁ → X)  → (λ d1 → f D₁) ≡ f
lemma-dumb f = begin   (λ d1 → f D₁) ≡⟨⟩ extensionality λ{ D₁ → refl }

open import Agda.Builtin.Sigma
_ : {X : Set} → ⦅ Option' ⦆ X ≈ Option X
_ = record { 
    to = λ{ (P₁ , snd) → Some (snd D₁)
          ; (P₂ , snd) → None } ;
    from = λ {None → P₂ , λ()
            ; (Some x) → P₁ , λ d1 → x} ; 
    from∘to = {!   !} ;
    {-begin (λ { None → P₂ , (λ ()) ; (Some x) → P₁ , (λ _ → x) })
    ((λ { (P₁ , snd) → Some (snd D₁) ; (P₂ , snd) → None }) (P₁ , snd))
                            ≡⟨⟩ (λ { None → P₂ , (λ ()) ; (Some x) → P₁ , (λ _ → x) }) Some (snd D₁) 
                            ≡⟨⟩ P₁ , (λ d1 → (snd D₁)) 
                            ≡⟨ {! cong₂ _,_ ? ?   !} ⟩ P₁ , snd --(λ {D₁  → (snd D₁)})  
                            ≡⟨⟩ refl
               ; (P₂ , snd) → {!  !}} ; -} 
    to∘from = λ {None → refl
               ; (Some x) → refl }}
{-
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
-- need isomorphism reasoning
_ : PFun Option' ≡ OptFun
_ = begin PFun Option' 
        ≡⟨⟩ record { 
                    F₀ = ⦅ Option' ⦆ ; 
                    F₁ = lift Option' ; 
                    identity = refl ; 
                    homomorphism = λ f g → refl }
        ≡⟨⟩ {!   !}
-} 


FunctorCat : Category
FunctorCat = record
                { Ob = Functor Agda Agda
                ; _⇒_ = λ F G → NatTrans F G
                ; _≋_ = λ N₁ N₂ → N₁ ≡ N₂
                ; _∘_ = {!   !}
                ; id = {!   !}
                ; idˡ = {!   !}
                ; idʳ = {!   !}
                ; ∘-assoc = {!   !}
                }

PolyCat : Category
PolyCat = record
        { Ob = Poly
        ; _⇒_ = Poly[_,_]
        ; _≋_ = λ p p' → p ≡ p'
        ; _∘_ = λ p q → q ⇒∘ₚ p
        ; id = (λ z → z) ⇒ₚ λ i z → z
        ; idˡ = λ {(onPos₁ ⇒ₚ onDir₁) → refl}
        ; idʳ = λ { (onPos₁ ⇒ₚ onDir₁) → refl }
        ; ∘-assoc = λ f g h → refl
        }

-- Could show that PolyCat is a subcategory of FunctorCat

module Slice where
    record SliceCategory(C : Category) (A : Ob C) : Set where
        field 
            -- obj : ∀ (X : Ob C) → ( ? ⇒ A)

-- Comonoids in (Poly,𝓎,◃) are catefories??
module ComonoidsAreCategories where

    record MonoidalCategory(C : Category) : Set where
        field
            I : Ob C
            _⨂_ : Ob C → Ob C → Ob C
            -- laws
    open MonoidalCategory

    record comonoid{C : Category}(M : MonoidalCategory C): Set where
        field
            m : Ob C
         --   ε : m → I

    record comonoidPoly : Set where
        m : Poly
        m = Set ▹ λ x → {!   !}
        
            
module Double where 
    -- Double category presentation as a matrix (List of List)
    --  
    record DoubleCategory : Set where
        field
            Ob : Set 
            _⇒ᵥ_ : Rel Ob
            _⇒ₕ_ : Rel Ob
        -- partial definition
        {-square : ∀ {a b c d : Ob}
                    (f : a ⇒ₕ b)
                    (f': c ⇒ₕ d)
                    (g : a ⇒ᵥ c)
                    (g': b ⇒ᵥ d) 
                    → {!   !} -}

    -- TODO Double Category (relation to 2-Category? )
    -- There is a way to get a Double Category from a 2-Category
    -- let both vertical and horizonal morphisms of C be the same as the 1 morphisms in the 2 category

    -- TODO Show the Double Category of Charts and Lenses

    open Poly.Poly
    record Square
            {p p' q q' : Poly} 
            (c₁ : Chart p p')
            (c₂ : Chart q q')
            (l₁ : Poly[ p , q ])
            (l₂ : Poly[ p' , q' ]): Set where
        open Chart c₁     renaming (onPos to f ; onDir to f♭)
        open Chart c₂     renaming (onPos to g ; onDir to g♭)
        open Poly[_,_] l₁ renaming (onPos to w ; onDir to w♯)
        open Poly[_,_] l₂ renaming (onPos to v ; onDir to v♯)
        field
        -- CURSED US OF o INSTEAD OF ∘
            square₁ : g o w ≡ v o f 

            -- this square relies on the equation in square₁
            -- .. not sure how to express this in agda
            -- Do I really need to break out cubical agda for this?
            square₂ :
             ∀ ( i : pos p)
               ( x : dir q (w i)) 
             → f♭ i (w♯ i x) ≡ {! v♯ (f i)  !} (g♭ (w i) x)

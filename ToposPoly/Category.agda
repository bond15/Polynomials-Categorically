{-# OPTIONS --type-in-type #-}
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
        --commute : ∀ {X Y}(f : X ⇒C Y) → ((η Y) ∘D (F₁ f)) ≋D (((G.F₁ f) ∘D η X))


-- natural transformations are polynomial functions
fun : {X : Set} → Option X → List X
fun None = []
fun (Some x) = [ x ]

open Category
open Functor
open NatTrans

_ : NatTrans  OptFun ListFun
_ = record { 
    η = λ X → fun ;
    commute = λ { f None → refl
                ; f (Some x) → refl } }
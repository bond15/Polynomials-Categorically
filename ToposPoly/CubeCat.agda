{-# OPTIONS --cubical #-}
{-# OPTIONS --type-in-type #-}
module CubeCat where

    module Double where 
    open import Poly
    open import Base using (_o_)
    open import Cubical.Core.Primitives
    REL : Set -> Set  -> Set 
    REL A B = A -> B -> Set 

    Rel :  Set -> Set 
    Rel A  = REL A A 

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
    refl : {A : Type} {a : A} → a ≡ a 
    refl {a = a} = λ i → a

    _ : 4 ≡ 4
    _ = refl

    funExt : {A B : Set}{f g : A → B} (p : (x : A) → f x ≡ g x) → f ≡ g
    funExt p i x = p x i    

    _ : {A B C : Set} {f g : A → B}{h : B → C} → f ≡ g → h o f ≡ h o g
    _ = λ p → funExt λ x  → {!   !}

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
             → f♭ i (w♯ i x) ≡  v♯ (f i) {! g♭ (w i) x   !}
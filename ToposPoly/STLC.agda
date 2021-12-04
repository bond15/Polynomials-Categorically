module STLC where 

-- See Datatypes of Datatypes Ch2
-- syntax of Types
data ⋆ : Set where 
    ι : ⋆
    _▹_ : ⋆ → ⋆ → ⋆

-- contexts as snoc lists
data Cx (X : Set) : Set where 
    ε : Cx X 
    _,_ : Cx X → X → Cx X
infixl 4 _,_     

-- de Bruijn indices
data _∈_(τ : ⋆) : Cx ⋆ → Set where 
    zero : ∀{Γ} → τ ∈ (Γ , τ)
    suc : ∀{Γ σ} → τ ∈ Γ → τ ∈ (Γ , σ)

data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where
    var : ∀{τ} → 
            τ ∈ Γ
            -----
            → Γ ⊢ τ
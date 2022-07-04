module DepDial where 
-- Is DepDial a displayed 3-Context?
open import Context

postulate
    L : Set 
    ⊸ : L → L → L
    _≤_ : L → L → Set

{-
record DepDial (C : Cxt) : Set where 
    open Cxt C
    field 
        U : pos
        V : (u : pos) → dir u
        cond : 
-}

record LDepDialSet : Set₁ where 
    constructor ⟨_,_,_⟩
    field 
        U : Set 
        V : U → Set 
        α : (u : U) → V u → L


record LDepDialSetMap (A B : LDepDialSet) : Set where 
        constructor _∧_st_
        open LDepDialSet A 
        open LDepDialSet B renaming (U to U'; V to V'; α to β)
        field 
            f : U → U' 
            F : (u : U) → (V' (f u)) → V u
            cond : (u : U)(v' : V' (f u)) → α u (F u v') ≤ β  (f u) v'

hmm : LDepDialSet → Cxt 
hmm ⟨ U , V , α ⟩ = U ▹ V st (λ u v → L) -- maps the typing of the fields, looses the relation α

open import Function
hmm2 : (A B : LDepDialSet) → LDepDialSetMap A B → Cxt[ hmm A , hmm B ]
hmm2 A B (f ∧ F st cond) = f ⇒ₚ F st relcond     -- id -- why? because the two sides of the `cond` relation have the same type so (L ≤ L) to L→L where the easiest choice is `id`
    where      
        open LDepDialSet A

        relcond : (p : Cxt.pos (hmm A)) → (d' : Cxt.dir (hmm B) (f p)) → L → L
        relcond p d' = {! α p   !} -- α u (F u v') ≤ β  (f u) v'  
                                    -- to
                                    -- α u (F u v') →  β  (f u) v'
                                    -- but how..

        lmap : L → L 
        lmap = {! α p   !}

other : Cxt → LDepDialSet
other (pos ▹ dir st rel) = ⟨ pos , dir , {! rel  !} ⟩
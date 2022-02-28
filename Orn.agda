module Orn where 

    module plain where 
        data PlainDesc : Set₁ where 
            -- sort of like Poly/Container
            arg : (A : Set) → (A → PlainDesc) → PlainDesc
            rec : PlainDesc → PlainDesc
            ret : PlainDesc


        data Two : Set where 
            one two : Two 

        -- ( Two ▹ λ x → ...)
        NatPlain : PlainDesc
        NatPlain = arg Two λ {one → ret
                            ; two → rec ret}


        open import Data.Product
        open import Data.Unit
        open import Data.Bool

        -- extension of a container
        ⦅_⦆ : PlainDesc → Set → Set 
        ⦅ arg A D ⦆ X = Σ A λ a → ⦅ D a ⦆ X
        ⦅ rec D ⦆   X = X × ⦅ D ⦆ X
        ⦅ ret ⦆     X = ⊤ 

        -- W type
        data PlainData (D : PlainDesc) : Set where 
            ⟨_⟩ : ⦅ D ⦆ (PlainData D) → PlainData D

        _ : ⦅ NatPlain ⦆ Bool
        _ = two , false , tt

        ℕ : Set 
        ℕ = PlainData NatPlain

        z : ℕ 
        z = ⟨ (one , tt) ⟩

        s : ℕ → ℕ 
        s = λ n → ⟨ (two , n , tt) ⟩


    module indexed where 
    {-
        data PlainDesc : Set₁ where 
            -- sort of like Poly/Container
            arg : (A : Set) → (A → PlainDesc) → PlainDesc
            rec : PlainDesc → PlainDesc
            ret : PlainDesc
    -}
        -- Indexed container like thing
        data Desc ( I : Set ) : Set₁ where 
            arg : (A : Set) → (A → Desc I) → Desc I 
            -- Is A used for anything other than cardinality?
            -- It determines the "branching factor" of a contstructor..
            -- But does it ever pass data along? 
            rec : I → (Desc I) → Desc I 
            ret : I → Desc I

        open import Data.Unit 
        open import Data.Bool 
        open import Data.Product
        open import Agda.Builtin.Equality public

        module depthTwo where
            Ty : Desc ⊤
            Ty = arg Bool λ{ false → arg Bool λ{ false → rec tt (ret tt) 
                                            ; true → rec tt (ret tt)}
                        ; true → arg Bool λ{ false → rec tt (ret tt) 
                                            ; true → rec tt (ret tt)}}

        -- can recreate ℕ by just using the trivial index ⊤
        {-
        NatPlain : PlainDesc
        NatPlain = arg Bool λ {false → ret
                                ; true → rec ret}
        -}
        NatDesc : Desc ⊤ 
        NatDesc = arg Bool λ { false → rec tt (ret tt)
                            ; true → ret tt}

        ⦅_⦆ : {I : Set} → Desc I → (I → Set) → I → Set 
        ⦅ arg A D ⦆ R i = Σ A λ a → ⦅ D a ⦆ R i
        ⦅ rec h D ⦆ R i = R h × ⦅ D ⦆ R i -- the index only changes here
        ⦅ ret o ⦆   R i = o ≡ i


        -- 𝒲 types
        data Data {I : Set}(D : Desc I) : I → Set where 
            ⟨_⟩ : ∀{ i : I} → ⦅ D ⦆ (Data D) i → Data D i


        ℕ : Set 
        ℕ = Data NatDesc tt

        z : ℕ 
        z = ⟨ true , refl ⟩

        s : ℕ → ℕ
        s n = ⟨ (false , n , refl) ⟩

        -- pattenr zero = z ..?  
        
        VecDesc : Set → Desc ℕ 
        VecDesc X = arg Bool λ{false → ret z -- for arguments that aren't indexes, here X, don't case split
                            ; true → arg  X λ{_ → arg ℕ λ{⟨ false , n , refl ⟩ → rec n (ret (s n))
                                                        ; ⟨ true , refl ⟩ → ret z}} }

        Vec : Set → ℕ → Set 
        Vec X n = Data (VecDesc X) n

        nil : {X : Set} → Vec X z 
        nil = ⟨ false , refl ⟩

        cons : {X : Set}{n : ℕ} → X → Vec X n → Vec X (s n)
        cons {n = n} x xs = ⟨ true , x , s n , xs , refl ⟩

        _ : Vec Bool (s (s z))
        _ = cons true (cons false nil)



    module indexedAlgebras where
        open indexed 
        open Desc
        open import Data.Product using (_,_)
        open import Data.Bool
        open import Data.Unit

        -- something something map of fibers?
        _⊆_ : {I : Set} → (I → Set) → (I → Set) → Set 
        _⊆_ {I} X Y = ∀(i : I) → X i → Y i

        -- x → y ⇒ F x → F y
        map :{I : Set}{X Y : I → Set} → (D : Desc I) → X ⊆ Y → ⦅ D ⦆ X ⊆ ⦅ D ⦆ Y
        map (arg A D) f i (a , d) = a , map (D a) f i d
        map (rec h D) f i (x , d) = f h x , map D f i d
        map (ret o)   f i refl = refl

        -- F X → X
        Alg : {I : Set} → Desc I → (I → Set) → Set 
        Alg D X = ⦅ D ⦆ X ⊆ X

        -- (alg : F X → X) → Fix F → X  
        {-# TERMINATING #-} -- how similar is this to proof algebras? ...
        fold : {I : Set}{X : I → Set} → (D : Desc I) → Alg D X → Data D ⊆ X 
        fold D ϕ = λ{ i ⟨ x ⟩ → ϕ i (map D (fold D ϕ)  i  x)}

        adda : ℕ → Alg NatDesc λ{ tt → ℕ }
        adda y = λ{tt (false , x , refl) → s x
                ; tt (true , refl) → y}

        _+_ : ℕ → ℕ → ℕ
        x + y = fold NatDesc (adda y) tt x

        _ : (s (s z)) + (s (s (s z))) ≡ (s (s (s (s (s z)))))
        _ = refl

        con : ∀{m : ℕ}{X : Set} → Vec X m → Alg (VecDesc X) (λ n → Vec X (n + m))
        con ys ⟨ false , n , refl ⟩ (true , x , ⟨ fst , snd₁ ⟩ , snd) = cons x {!  snd !}
        con ys ⟨ true , refl ⟩ _ = ys

        _++_ : ∀{n m : ℕ}{X : Set} → Vec X n → Vec X m → Vec X (n + m)
        _++_ {X} xs ys = {! fold VecDesc   !}

    

    module Ornaments where 
        -- cool way to represent a fiber !
        -- definitional equality rather than propositional equality
        -- for f : J → I and i : I,
        -- Σ[ j ∈ J ] (f j ≡ i) 
        data Inv {I J : Set} (e : J → I) : I → Set where 
            inv : (j : J) → Inv e (e j)

        -- example
        open import Data.Nat renaming (ℕ to 𝕟)
        open import Data.Bool
        open import Data.Unit 

        open indexed
        open Desc renaming (arg to darg ; rec to drec ; ret to dret)

        evenb : 𝕟 → Bool 
        evenb zero = true
        evenb (suc zero) = false
        evenb (suc (suc x)) = evenb x

        _ : Inv evenb true
        _ = inv 4 -- but inv 3 fails to typecheck!
        open indexed using (Desc)
        
        data Orn {I J : Set} (e : J → I) : Desc I → Set₁ where 
            arg : {A : Set}{D : A → Desc I} → 
                ((a : A) → Orn e (D a)) → Orn e (arg A D)
            rec : {h : I}{D : Desc I} → 
                Inv e h → Orn e D → Orn e (rec h D)
            ret : {o : I} → 
                Inv e o → Orn e (ret o)
            new : {D : Desc I} → 
                (A : Set) → ((a : A) → Orn e D) → Orn e D

        ! : {X : Set} → X → ⊤ 
        ! _ = tt
        
        ListOrn : Set → Orn ! NatDesc
        ListOrn X = arg λ{ false → new X λ{ _ → rec (inv tt) (ret (inv tt)) }
                        ; true → ret (inv tt)}

        orn : {I J : Set}{e : J → I}{D : Desc I} → Orn e D → Desc J 
        orn (arg {A = A} O) = darg A (λ a → orn (O a))
        orn (rec (inv j) O) = drec j (orn O)
        orn (ret (inv j)) = dret j
        orn (new A O) = darg A (λ a → orn (O a))

        data Foo : Set where 
            foo : Foo 

        _ : Desc ⊤ 
        _ = orn (ListOrn Foo)

        open indexedAlgebras
        open import Function
        open import Data.Product
        open import Data.Bool


        𝓧 : {I J : Set}{e : J → I}{D : Desc I}{O : Orn e D} → Alg (orn O) (Data D ∘ e)
        𝓧  {O = O} j os = ⟨ erase O j os ⟩ where 
            erase : {I J : Set}{e : J → I}{D : Desc I} {R : I → Set} → (O : Orn e D) → (⦅ orn O ⦆ ( R ∘ e)) ⊆ ((⦅ D ⦆ R) ∘ e )
            erase (arg O) j (a , os) = a , erase (O a) j os
            erase (rec (inv h) O) j (r , os) = r , erase O j os
            erase (ret (inv j)) j refl = refl
            erase (new A O) j (a , os) = erase (O a) j os


        ∥_∥ : {I J : Set}{e : J → I}{D : Desc I}{O : Orn e D}{j : J} → Data (orn O) j → Data D (e j)
        ∥_∥ {O = O}{j = j} = (fold (orn O) 𝓧) j 

        ex₁ : Data (orn (ListOrn Foo)) tt
        ex₁ = ⟨ (false , foo , (⟨ (true , refl) ⟩ , refl)) ⟩

        t : Data NatDesc tt
        t = ∥_∥ {O = ListOrn Foo} ex₁ -- length funtion on lists

        t' : Data NatDesc tt
        t' = s z

        _ : t ≡ t' 
        _ = refl

        -- vector to list
            
        VecOrn : Set → Orn (λ j → tt) NatDesc 
        VecOrn = {!   !}

        VecDesc' : Set → Desc ℕ 
        VecDesc' X = arg Bool λ{false → ret z -- for arguments that aren't indexes, here X, don't case split
                            ; true → arg  X λ{_ → arg ℕ λ{⟨ false , n , refl ⟩ → rec n (ret (s n))
                                                        ; ⟨ true , refl ⟩ → ret z}} } 
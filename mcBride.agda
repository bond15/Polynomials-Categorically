module mcBride where

-- Connor mcBride cs 410 2017

data Zero : Set where

--data One : Set where one : One
record One : Set where
  constructor <>

data Two : Set where tt ff : Two

So : Two -> Set
So tt = One
So ff = Zero

data _+_ (A B : Set) : Set where
  inj₁ : A -> A + B
  inj₂ : B -> A + B

data _*_ (A B : Set) : Set where
  _,_ : A -> B -> A * B

data Poly (X : Set) : Set where
  var : X -> Poly X
  const : Two -> Poly X -- tt for 1 type, ff for 0 type
  _+p_ _*p_ : Poly X -> Poly X -> Poly X


-- substitute in a type for the polynomial
Eval : {X : Set} -> (X -> Set) -> Poly X -> Set
Eval f (var x) = f x
Eval f (const x) = So x
Eval f (x +p y) = Eval f x + Eval f y
Eval f (x *p y) = Eval f x * Eval f y
-- C-c C-c  case split on vars
-- C-c C-a  try to solve goal
-- C-c C-,  show context
eval : {X : Set} (u v : X -> Set)(p : Poly X) ->
        ((x : X) -> u x -> v x) ->
        Eval u p -> Eval v p
eval u v (var i) f x = f i x -- map old variables to new variables
eval u v (const b) f x = x -- constants in polynomial do not change when variables change
-- ^^ interesting cases
eval u v (p +p q) f (inj₁ x) = inj₁ (eval u v p f x)
eval u v (p +p q) f (inj₂ x) = inj₂ (eval u v q f x)
eval u v (p *p q) f (x , x₁) = eval u v p f x , eval u v q f x₁

data μ (p : Poly One) : Set where
  <_> : Eval (λ _ -> μ p) p -> μ p -- substitute all vars with μ p (fixpoint of functor?)

fold : (p : Poly One){T : Set}
        -> (Eval (λ _ -> T) p -> T)  -- algebra  F[T] -> T or here p[T] -> T
        -> μ p
        -> T
fold p {T} alg < x >  = alg (evenFold p x)
  where
    evenFold :  (q : Poly One) -> Eval (λ _ -> μ p) q -> Eval (λ _ -> T ) q
    evenFold (var x₁) x = fold p alg x
    evenFold (const x₁) x = x
    evenFold (q +p q₁) (inj₁ x) = inj₁ (evenFold q x)
    evenFold (q +p q₁) (inj₂ x) = inj₂ (evenFold q₁ x)
    evenFold (q *p q₁) (x , x₁) = evenFold q x , evenFold q₁ x₁

ex : Set
ex = Eval (λ _ -> One) (var tt +p var ff) -- One + One

maybeF : Poly One
maybeF = const tt +p var <>

ex₂ : Set
ex₂ = Eval (λ _ -> Two) maybeF

NatF : Poly One
NatF = const tt +p var <>

ℕ : Set
ℕ = μ NatF

z : ℕ
z = < inj₁ <> > -- In (inl Unit)

suc : ℕ -> ℕ
suc n = < inj₂ n >


TreeF : Poly One
TreeF = const tt +p (var <> *p var <>)

Tree : Set
Tree = μ TreeF

leaf : Tree
leaf = < inj₁ <> >

node : Tree -> Tree -> Tree
node l r = < inj₂ (l , r) >

--

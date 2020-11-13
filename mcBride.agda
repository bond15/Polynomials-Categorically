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

data μ (p : Poly One) : Set where
  <_> : Eval (λ _ -> μ p) p -> μ p -- substitute all vars with μ p (fixpoint of functor?)

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

module mcBride where
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong)
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


-- substitute in a type for the polynomial's variable
Eval : {X : Set} -> (X -> Set) -> Poly X -> Set
Eval f (var x) = f x
-- Zero or One
Eval f (const x) = So x
-- +p to +
Eval f (x +p y) = Eval f x + Eval f y
-- *p to *
Eval f (x *p y) = Eval f x * Eval f y
-- C-c C-c  case split on vars
-- C-c C-a  try to solve goal
-- C-c C-,  show context

-- fmap for all types expressed by polynomials
-- essentially "deriving Functor"
eval : {X : Set} (u v : X -> Set)(p : Poly X) ->
        ((x : X) -> u x -> v x) ->
        Eval u p -> Eval v p
eval u v (var i) f x = f i x -- map old variables to new variables
eval u v (const b) f x = x -- constants in polynomial do not change when variables change
-- remember constants are just Zero and One types
-- ^^ interesting cases
eval u v (p +p q) f (inj₁ x) = inj₁ (eval u v p f x)
eval u v (p +p q) f (inj₂ x) = inj₂ (eval u v q f x)
eval u v (p *p q) f (x , x₁) = eval u v p f x , eval u v q f x₁


-- making polynomials "recursive"
-- Why only poly One here? just one variable polynomials?
-- can only construct var <> aka var unit
-- one choice of variable
data μ (p : Poly One) : Set where
  <_> : Eval (λ _ -> μ p) p -> μ p
  -- substitute all vars with μ p (fixpoint of functor?)

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

TreeF : Poly One
TreeF = const tt +p (var <> *p var <>) -- 1 + (X * X)

Tree : Set
Tree = μ TreeF

leaf : Tree
leaf = < inj₁ <> >

--node : Tree -> Tree -> Tree
pattern node l r = < inj₂ (l , r) >

Diff : Poly One -> Poly One
Diff (var x) = const tt -- One
Diff (const x) = const ff -- Zero
Diff (p +p q) = Diff p +p Diff q
Diff (p *p q) = (Diff p *p q) +p (p *p Diff q)

Context : Poly One -> Set
Context p = List (Eval ((λ _ -> μ p )) (Diff p))

{-
_[_] : {X : Set} (p : Poly One) -> (X : Set) -> Set
p [ x ] = Eval (λ _ -> x) p

plug : {X : Set}
      (p : Poly One) ->
      X ->
      (Diff p) [ X ] ->
      p [ X ]
plug p x p' = {!   !} -}

plug : {X : Set} (p : Poly One) ->
      X -> -- a value to fill in
      Eval (λ _ -> X) (Diff p) -> -- the context around the hole
      Eval (λ _ -> X) p
plug (var <>) x p' = x -- put the element in the hole
plug (p +p q) x (inj₁ p') = inj₁ (plug p x p')
plug (p +p q) x (inj₂ q') = inj₂ (plug q x q')
plug (p *p q) x (inj₁ (p'x , qx)) = plug p x p'x , qx
plug (p *p q) x (inj₂ (px , q'x)) = px , plug q x q'x


plugs : (p : Poly One) -> μ p -> Context p -> μ p
plugs p t [] = t
plugs p t (t' :: t's) = plugs p < plug p t t' > t's


treeContextType : Set
treeContextType =  Eval (λ _ -> Tree) (Diff TreeF)
-- Zero + ((1 * Tree) + (Tree * 1))

--ltree : Tree -> treeContextType
pattern ltree r = inj₂ (inj₁ (<> , r) )

--rtree : Tree -> treeContextType
pattern rtree l = inj₂ (inj₂ (l , <>))

subTree : Tree
subTree = node leaf (node leaf leaf)

treeContext : List treeContextType
treeContext = (ltree leaf) :: ((rtree (node leaf leaf)) :: [])

result : Tree
result = node
          (node leaf leaf)
          (node
            (node leaf (node leaf leaf))
            leaf)

prf : plugs TreeF subTree treeContext ≡ result
prf = refl

-- navigating the tree

Loc : Set
Loc = Tree * Context TreeF

left : Loc -> Loc
left (node l r , c) = l , (rtree r :: c )
left x = x -- at a leaf, can't traverse further

right : Loc -> Loc
right (node l r , c) = r , (ltree l :: c)
right x = x -- at a leaf, can't traverse further

up : Loc -> Loc
up (t , (ltree r :: c)) = (node t r , c)
up (t , (rtree l :: c)) = (node l t , c)
up x = x -- at the top, can't traverse further

top : Tree -> Loc
top t = (t , [])

get : Loc -> Tree
get (t , c) = t

-- no matter where you are in the tree,
-- return the whole reconstructed tree
whole : Loc -> Tree
whole (t , c) = plugs TreeF t c

modify : (Tree -> Tree) -> Loc -> Loc
modify f (t , c) = (f t , c)


infixl 30 _=>_
_=>_ : {A B C : Set} (f : A -> B) -> (g : B -> C) -> A -> C
f => g = λ x -> g (f x)


-- Tree edit sequences
editSequence : Tree -> Tree
editSequence = (top => right => left => (modify λ _ -> leaf) => up => whole)

_ : Tree
_ = editSequence result


--lefttt (node l r , c) = {!   !}
--lefttt (leaf , c) = {!   !}

{-

So derivatives of types are a thing and apparently they are useful.

Taking the derivative of a type gives you "the type of one hole contexts" of your original type.

What it gives you is a generic way to traverse your data type from the perspective of a 'hole' (akin to pointers).

ex) If I had a tree data type, I would get a way to write primative combinators
'left', 'right', 'up', 'down', etc.

-- binary tree with no data
data Tree = Leaf | Node Tree Tree

this is equivalently expressed as a polynomial

Tree(X)= 1 + ( X * X )

where 1 ≅ Leaf
(X * X) ≅ Node Tree Tree

or

Tree(X) = 1 + X²

We know how to take the derivative of polynomials

Derivative(Tree) = 0 + (1 * X + X * 1) ≅ 2X

This is isomorphic to type

type Tree' X = (Unit :*: X) :+: (X :*: Unit)

This Tree' type represents the idea of
  Either
    the hole is pointing to the left subtree (and we record what the right subtree is)
  or
    the hole is pointing to the right subtree (and we record what the left subtree is)

If you have a List of Tree' elements, this represents a traced path from the root node to the hole

And if you have a trace from the root node to the hold AND a subtree to fill the hole, THEN you can reconstruct the whole tree.

-}


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

NatF : Poly One
NatF = const tt +p var <> -- 1 + X

ℕ : Set
ℕ = μ NatF

z : ℕ
z = < inj₁ <> > -- In (inl Unit)

suc : ℕ -> ℕ
suc n = < inj₂ n >






record ν (p : Poly One) : Set where
  coinductive
  field
    out : Eval (λ _ -> ν p) p



-- derivatives






--

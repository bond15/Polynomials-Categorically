module foo where


data Bool : Set where
  tt ff : Bool


not : Bool -> Bool -> Bool
not tt = λ y -> y
not ff = λ z → z

module Id where

open import Nat

data Id {A : Set} : A -> A -> Set where
    refl : (x : A) -> Id x x


variable A : Set
variable a b : A

sym : (Id a b) -> (Id b a)
sym (refl a) = refl a



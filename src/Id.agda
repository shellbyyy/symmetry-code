module Id where

open import Nat
open import Op using (id)

open import Agda.Primitive

data Id {l :Level} {A : Set l} : A -> A -> Set l where
    refl : (x : A) -> Id x x


variable l ll : Level
variable A : Set l
variable a b c : A

sym : (Id a b) -> (Id b a)
sym (refl a) = refl a

trans : (Id a b) -> (Id b c) -> (Id a c)
trans (refl a) (refl a) = refl a
-- why does this error?
-- trans (refl a) p = p

-- unsure why this doesn’t works hmmm
trp : (T : A -> Set ll) -> (Id a b) -> (T a) -> (T b)
trp _ (refl a) = id

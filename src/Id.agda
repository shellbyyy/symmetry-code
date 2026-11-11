module Id where

open import Nat
open import Op using (id)

open import Agda.Primitive

data Id {l : Level} {A : Set l} : A -> A -> Set l where
    refl : (a : A) -> Id a a

-- how to use this and also be able to use (refl' a) as expression?
-- data Id {l : Level} {A : Set l} (a : A) : A -> Set l where
--     instance refl : Id a a
    

infix 6 _＝_
_＝_ : {l : Level} {A : Set l} -> A → A → Set l
(a ＝ b) = Id a b

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

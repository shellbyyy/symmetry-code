module Id where

open import Nat
open import Op using (id)

open import Agda.Primitive

module _
    {l : Level}
    {A : Set l}
  where

    data Id : A -> A -> Set l where
        refl : (a : A) -> Id a a

    -- how to use this and also be able to use (refl' a) as expression?
    -- data Id {l : Level} {A : Set l} (a : A) : A -> Set l where
    --     instance refl : Id a a

    infix 6 _＝_
    _＝_ :  A → A → Set l
    (a ＝ b) = Id a b

module _ 
    {l : Level}
    {A : Set l}
    (a b c : A)
  where
    sym : (Id a b) -> (Id b a)
    sym (refl a) = refl a

    trans : (Id a b) -> (Id b c) -> (Id a c)
    trans (refl a) p = p

    trp : {l' : Level} (T : A -> Set l') -> (Id a b) -> (T a) -> (T b)
    trp _ (refl a) = id

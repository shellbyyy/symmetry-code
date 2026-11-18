module Sym.Sum where

open import Agda.Primitive

module _
  where
    -- NOTE: see https://spcfox.github.io/agda-unimath/foundation.dependent-pair-types.html
    -- TODO: not sure why ⊔ the max of them? maybe because l' must be included??
    data Σ {l l' : Level} (X : Set l) (Y : X → Set l') : Set (l ⊔ l') where
        _,_ : (a : X) -> (b : Y a) -> Σ X Y

module _ 
  where
    -- aaaaah why the same here as in Id.agda where X,Y,l,l' in module gives meta variable 
    -- error/invisible goal wtf
    fst : {l l' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> (Σ X Y) -> X
    fst (a , _) = a

    snd : {l l' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> (z : Σ X Y) -> Y (fst z)
    snd (a , b) = b

    -- TODO: define by using rec function




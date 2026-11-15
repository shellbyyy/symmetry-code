module Prod where

open import Id

open import Agda.Primitive

module _ 
    {l l' : Level}
    (X : Set l)
    (Y : Set l')
  where

  ap : {x x' : X} (f : X -> Y) -> (Id x x') -> (Id (f x) (f x'))
  ap f (refl x) = refl (f x)

module _
    {ll : Level}
    (X : Set ll)
    (Y : Set ll)
  where

  ap-communion : {x x' x'' : X} (f : X -> Y) -> (p : Id x x') -> (p' : Id x' x'') 
    -> Id (ap f (trans p p')) (trans (ap f p) (ap f p'))


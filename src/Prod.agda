module Prod where

open import Id

open import Agda.Primitive

variable l1 l2 : Level
variable X : Set l1
variable Y : Set l2

ap : (f : X -> Y) -> {x x' : X} -> (Id x x') -> (Id (f x) (f x'))
ap f (refl x) = refl (f x)

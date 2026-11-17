module Sym.Op where

open import Sym.Nat.Base using (Nat)

open import Agda.Primitive

module _
    {l : Level}
    {X : Set l}
  where

  iter : Nat -> (X -> X) -> (X -> X)
  iter Nat.zero _ x = x
  iter (Nat.suc n) f x = f ((iter n f) x)

  id : X -> X
  id x = x

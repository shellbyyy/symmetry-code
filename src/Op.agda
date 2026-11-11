module Op where

open import Nat.Base using (Nat)

variable X : Set

iter : Nat -> (X -> X) -> (X -> X)
iter Nat.zero _ x = x
iter (Nat.suc n) f x = f ((iter n f) x)


module Op where

open import Nat.Base using (Nat)

open import Agda.Primitive

variable l : Level
variable X : Set l

iter : Nat -> (X -> X) -> (X -> X)
iter Nat.zero _ x = x
iter (Nat.suc n) f x = f ((iter n f) x)

id : X -> X
id x = x
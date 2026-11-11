module Nat.Operators where

open import Nat.Base using (Nat; zero; one; suc)
open import Op using (iter)

_+_ : Nat -> Nat -> Nat
_+_ a zero = a
_+_ a (suc b) = (suc a) + b

_*_ : Nat -> Nat -> Nat
_*_ a b = iter b (_+_ a) zero

_^_ : Nat -> Nat -> Nat
_^_ a b = iter b (_*_ a) one



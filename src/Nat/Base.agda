module Nat.Base where

data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

one : Nat
one = suc zero

n0 = zero
n1 = suc zero
n2 = suc n1
n3 = suc n2
n4 = suc n3
n5 = suc n4


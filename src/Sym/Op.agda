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

    -- TODO: make this function that accepts argument X
    id : X -> X
    id x = x

module _
    {l : Level}
  where
    id' : (X : Set l) -> (X -> X)
    id' X = id

module _ 
  where
    -- stolen from https://agda.github.io/agda-stdlib/v2.1/Function.Base.html#1136
    _∘'_ : ∀ {la lb lc : Level} {A : Set la} {B : A → Set lb} {C : {x : A} → B x → Set lc} →
          (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
          ((x : A) → C (g x))
    f ∘' g = λ x → f (g x)


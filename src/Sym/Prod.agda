module Sym.Prod where

open import Sym.Id
open import Sym.Op using (id)

open import Agda.Primitive

-- definition 2.6.1
module _ 
  where
  -- TODO: why does this break if  l l' X Y are defined in module??????
  ap :{l l' : Level} {X : Set l} {Y : Set l'} {x x' : X} (f : X -> Y) -> (x ＝ x') -> (Id (f x) (f x'))
  ap f (refl x) = refl (f x)

-- construction 2.6.2
module _
    {ll : Level}
    (X : Set ll)
    (Y : Set ll)
  where
  ap-communion : {x x' x'' : X} (f : X -> Y) -> (p : Id x x') -> (p' : Id x' x'') 
    -> (ap f (p' ∘ p)) ＝ ((ap f p') ∘ (ap f p))
  ap-communion f (refl a) (refl a) = refl (refl (f a))

  ap-inverse-compat : {x x' x'' : X} (f : X -> Y) -> (p : Id x x') -> Id (ap f (sym p)) (sym (ap f p))
  ap-inverse-compat f (refl a) = refl (refl (f a))

  ap-id-compat : {x x' x'' : X} (f : X -> Y) -> (p : Id x x') -> Id (ap id p) p
  ap-id-compat f (refl a) = refl (refl a)



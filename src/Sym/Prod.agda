module Sym.Prod where

open import Sym.Id
open import Sym.Op

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


-- exercise 2.6.3
module _
    {l l' l'' : Level}
    {X : Set l}
    {T : X -> Set l'}
    {A : Set l''}
    {f : A -> X}
  where

    it : {a a' : A} -> (p : a ＝ a') -> Id (trp (T ∘' f) p) (trp T (ap f p))
    it (refl _) = refl id
    -- it (refl a) = refl (id' ((T ∘' f) a))

-- definition 2.6.4
module _ 
  where
    ptw : {l l' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> (f g : (x : X) -> Y x) -> (f ＝ g) -> ((x : X) -> (f x) ＝ (g x))
    ptw f f (refl x) = λ x → refl (f x)

-- definition 2.6.5
module _ 
  where
    help : {l : Level} -> {A : Set l} -> {a b : A} -> (p : a ＝ b) -> ((p ∘ (refl a)) ＝ ((refl b) ∘ p))
    help (refl b) = refl (refl b)

    ns : {l l' : Level} -> {X : Set l} -> {Y : Set l'} -> {f g : X -> Y} -> (h : (w : X) -> (f w) ＝ (g w)) -> {x x' : X} -> (p : x ＝ x') -> ((h x') ∘ (ap f p)) ＝ ((ap g p) ∘ (h x))
    -- how to tell agda that (h a) ∘ (refl a) = (h a) and (refl a) ∘ (h a) = (h a) exists? ⇒ like in ex 2.5.3
    -- this is really weird? how to do this nicer?
    ns h (refl a) = help (h a)



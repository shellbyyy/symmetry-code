module Sym.IdFam where

open import Sym.Id
open import Sym.Op using (id'; id)
open import Sym.Prod using (ap)

open import Agda.Primitive

-- definition 2.7.1
module _
  where
    -- as definition
    id-over : {l l' : Level} -> {X : Set l} -> (Y : X -> Set l') -> {x x' : X} -> (p : x ＝ x') -> (y : Y x) -> (y' : Y x') -> Set l'
    id-over Y p y y' = (trp Y p y) ＝ y'

    data IdOver {l l' : Level} {X : Set l} {Y : X -> Set l'} {x x' : X} : (p : x ＝ x') -> (y : Y x) -> (y' : Y x') -> Set (l ⊔ l') where 
        id-over' : (p : x ＝ x') -> (y : Y x) -> (y' : Y x') -> IdOver p y y'
        -- TODO: something like this is needed for id-over-eq-id
        -- id-over-refl (refl x) y y' = Id y y'

    -- id-over-eq-id : {l l' l'' : Level} -> {X : Set l} -> (Y : X -> Set l') -> {x x' : X} (p : x ＝ x') -> {y : Y x} -> {y' : Y x'} -> (IdOver p y y') -> (trp Y p y) ＝ y'
    -- id-over-eq-id Y (refl x) = {! !}

-- definition 2.7.6
module _ 
  where
    apd : {l l' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> {x x' : X} -> (f : (w : X) -> Y w) -> (p : x ＝ x') -> id-over Y p (f x) (f x')
    apd f (refl x) = refl (f x)

-- TODO: exercise 2.7.5
-- as we make id-over alias for a Id type which this is possible for?? idk try this mabye

-- definition 2.7.7
module _ 
  where
    apap : {l l' l'' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> {Z : Set l''} -> (g : (w : X) -> (Y w) -> Z) -> {x x' : X} -> {y : Y x} -> {y' : Y x'} -> (p : x ＝ x') -> (q : id-over Y p y y') -> (g x) y ＝ (g x') y'
    apap g (refl x) (refl y) = refl (g x y)


-- definition 2.7.8
module _
  where
    it : {l l' l'' : Level} -> {X : Set l} -> {Y : X -> Set l'} -> {Z : Set l''} -> (g : (w : X) -> (Y w) -> Z) -> (x : X) -> {y y' : Y x} -> (q : Id y y') -> apap g (refl x) q ＝ ap (g x) q
    it g x (refl a) = refl (refl (g x a))



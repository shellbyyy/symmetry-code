module Sym.Id where

open import Sym.Nat using (Nat; zero; suc; one)
open import Sym.Op using (id; id')

open import Agda.Primitive

module _
    {l : Level}
    {A : Set l}
  where

    data Id : A -> A -> Set l where
        refl : (a : A) -> Id a a

    -- how to use this and also be able to use (refl' a) as expression?
    -- data Id {l : Level} {A : Set l} (a : A) : A -> Set l where
    --     instance refl : Id a a

    infix 6 _＝_
    _＝_ :  A → A → Set l
    (a ＝ b) = Id a b

module _ 
    {l : Level}
    {A : Set l}
    {a b c : A}
  where
    sym : (Id a b) -> (Id b a)
    sym (refl a) = refl a

    trans : (Id a b) -> (Id b c) -> (Id a c)
    trans (refl a) p = p
    -- trans (refl a) (refl a) = (refl a)

    _∘_ : (Id b c) -> (Id a b) -> (Id a c)
    _∘_ y x = trans x y

    trp : {l' : Level} (T : A -> Set l') -> (Id a b) -> (T a) -> (T b)
    trp _ (refl a) = id

-- exercise 2.5.3
module _
    {l : Level}
    {A : Set l}
    {a b c d : A}
  where
    e-1 : (p : a ＝ b) -> (((refl b) ∘ p) ＝ p)
    e-1 (refl b) = refl (refl b)

    e-2 : (p : a ＝ b) -> ((p ∘ (refl a)) ＝ p)
    e-2 (refl a) = refl (refl a)

    e-3 : (p : a ＝ b) -> (q : b ＝ c) -> (r : c ＝ d) -> ((r ∘ (q ∘ p)) ＝ ((r ∘ q) ∘ p))
    e-3 (refl a) (refl a) (refl a) = refl (refl a)

    -- FIXME: sym p is "invisible goal" ???
    e-4 : (p : a ＝ b) -> (((sym p) ∘ p) ＝ (refl a))
    e-4 (refl a) = refl (refl a)

    e-5 : (p : a ＝ b) -> ((p ∘ (sym p)) ＝ (refl b))
    e-5 (refl b) = refl (refl b)

    e-6 : (p : a ＝ b) -> ((sym (sym p)) ＝ p)
    e-6 (refl a) = refl (refl a)

-- exercise 2.5.5
module _exercise
    {l l' : Level}
    {X : Set l}
    {T : X -> Set l'} 
    {a b c : X}
  where
    -- stolen from https://agda.github.io/agda-stdlib/v2.1/Function.Base.html#1136
    _∘'_ : ∀ {la lb lc : Level} {A : Set la} {B : A → Set lb} {C : {x : A} → B x → Set lc} →
          (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
          ((x : A) → C (g x))
    f ∘' g = λ x → f (g x)

    it : (e : a ＝ b) -> (e' : b ＝ c) -> ((trp T (e' ∘ e)) ＝ ((trp T e' ) ∘' (trp T e)))
    it (refl a) (refl a) = refl (id' (T a))


-- exercise 2.5.6
module _exercise'
    {l l' : Level}
    {X : Set l}
    {Y : Set l'}
    {a b c : X}
  where
    -- TODO: how to make const type family easier?
    Y' : X -> Set l'
    Y' _ = Y

    it : (p : a ＝ b) -> ((trp Y' p) ＝(id' Y))
    it (refl a) = refl (id' Y)




    

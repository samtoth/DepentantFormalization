{-# OPTIONS --cubical #-}
module Categories.NaturalTransformation.Base where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor


open Category
open Functor


NatTrans : ∀ {ℓC ℓC' ℓD ℓD'}
             {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
             (F G : Functor C D) → Type (ℓ-max ℓC ℓD')
NatTrans {C = C}  {D = D} F G = ∀ (a : C .Ob) → D [ F .F0 a , G .F0 a ]

record IsNatural {ℓC ℓC' ℓD ℓD'}
             {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
             {F G : Functor C D} {{𝓓cat : IsCategory D}}
             (α : NatTrans F G) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
  open IsCategory 𝓓cat
  field
    nat : ∀ {a b : C .Ob} → {f : C [ a , b ]} → (G .F1 f ∘ α a) ≡ (α b ∘ F .F1 f)

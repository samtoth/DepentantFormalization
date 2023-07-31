{-# OPTIONS --cubical #-}
module Categories.Functor.Base where

open import Foundations.Prelude

open import Categories.Category

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


record Functor (C : Category ℓC ℓC') (D : Category ℓD ℓD') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where

  open Category

  field
    F0 : C .Ob → D .Ob
    F1 : ∀ {a b} → C [ a , b ] → D [ F0 a , F0 b ]

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

open Functor

swapOp : ∀ {𝓒 : Category ℓC ℓC'} {𝓓 : Category ℓD ℓD'} → Functor (𝓒 ^op) 𝓓 → Functor 𝓒 (𝓓 ^op)
Functor.F0 (swapOp x) = x .F0
Functor.F1 (swapOp x) = λ f → sym (x .F1 (sym f))

swapOp' : ∀ {𝓒 : Category ℓC ℓC'} {𝓓 : Category ℓD ℓD'} → Functor 𝓒 (𝓓 ^op) → Functor (𝓒 ^op) 𝓓
F0 (swapOp' x) = x .F0
F1 (swapOp' x) (sym f) = unsym (x .F1 f)

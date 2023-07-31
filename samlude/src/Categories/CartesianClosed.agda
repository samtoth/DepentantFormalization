{-# OPTIONS --cubical #-}
module Categories.CartesianClosed where

open import Foundations.Prelude
open import Foundations.Equiv

open import Categories.Category

open import Categories.Diagram.Two

record CC {ℓ ℓ'} (𝓒 : Category ℓ ℓ') ⦃ 𝓒cat : IsCategory 𝓒 ⦄ ⦃ 𝓒× : HasProducts 𝓒 ⦄ : Type (ℓ-max ℓ ℓ')  where
  open Category 𝓒
  field
    [_,_] : ∀ (A B : Ob) → Ob
    [un]curry : ∀ {A B C : Ob} → Hom (A × B) C ≃ Hom A ([ B , C ])

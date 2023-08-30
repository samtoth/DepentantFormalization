{-# OPTIONS --cubical #-}
module Foundations.Equiv where

open import Foundations.Prelude
open import Foundations.Homotopy


fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ A \ x → f x ≡ y


-- We make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
    equiv-proof : (y : B) → isContr {ℓ-max ℓ ℓ'} (fiber f y)

open isEquiv public


_≃_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) λ f → (isEquiv f)


record Iso : Type where

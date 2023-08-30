{-# OPTIONS --cubical #-}
module Foundations.Homotopy where

open import Foundations.Prelude

variable
 ℓ : Level

data ℍ : Type where
  ⁻2  : ℍ
  suc : ℍ → ℍ

is-ℍ-Type : ℍ → Type ℓ → Type ℓ
is-ℍ-Type {ℓ} ⁻2 X = Σ X λ x → ∀ y → Path {ℓ} X x y
is-ℍ-Type {ℓ} (suc ⁻2) X = ∀ (x y : X) → Path {ℓ} X x y
is-ℍ-Type {ℓ} (suc (suc h)) X = (x y : X) → is-ℍ-Type {ℓ} (suc h) (Path {ℓ} X x y)

isContr : Type ℓ → Type ℓ
isContr = is-ℍ-Type ⁻2

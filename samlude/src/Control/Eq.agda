{-# OPTIONS --cubical --cumulativity #-}
module Control.Eq where

open import Foundations.Prelude
open import Foundations.Decidable

record Eq {ℓ} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    _≟_ : (a b : A) → Dec {ℓ} (a ≡ b)

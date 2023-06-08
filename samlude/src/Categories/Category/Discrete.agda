{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Discrete where

open import Foundations.Prelude

open import Categories.Category.Base

data Id {ℓ ℓ'} (A : Type ℓ) : A → A → Type (ℓ-max ℓ ℓ') where
  refl : ∀ {x : A} → Id A x x


Discrete : ∀ {ℓ ℓ'} → Type ℓ → Category ℓ (ℓ-max ℓ ℓ')
Discrete x = Cat x (Id x)


instance
  DiscreteCAT : ∀ {x} → IsCategory (Discrete x)
  IsCategory.Id DiscreteCAT = refl
  (DiscreteCAT IsCategory.∘ refl) refl = refl

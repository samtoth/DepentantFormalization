{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Discrete where

open import Foundations.Prelude

open import Categories.Category.Base

data Id {ℓ} (A : Type ℓ) : A → A → Type ℓ where
  refl : ∀ {x : A} → Id A x x


Discrete : ∀ {ℓ} → Type ℓ → Category ℓ ℓ
Discrete x = Cat x (Id x)


instance
  DiscreteCAT : ∀ {x} → IsCategory (Discrete x)
  IsCategory.Id DiscreteCAT = refl
  (DiscreteCAT IsCategory.∘ refl) refl = refl

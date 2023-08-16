{-# OPTIONS --cubical #-}
module Categories.Category.Discrete where

open import Foundations.Prelude

open import Categories.Category.Base

data Id {ℓ} (A : Type ℓ) : A → A → Type ℓ where
  Refl : ∀ {x : A} → Id A x x


Discrete : ∀ {ℓ} → Type ℓ → Category ℓ ℓ
Discrete x = Cat x (Id x)


instance
  DiscreteCAT : ∀ {ℓ} {x : Type ℓ} → IsCategory (Discrete x)
  IsCategory.Id DiscreteCAT = Refl
  (DiscreteCAT IsCategory.∘ refl) Refl = refl

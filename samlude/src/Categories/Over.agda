{-# OPTIONS --cubical --cumulativity #-}
module Categories.Over where

open import Foundations.Prelude

open import Categories.Category
open Category

_/_ : ∀ {ℓ} {ℓ'} → (c : Category ℓ ℓ') → Ob c → Category (ℓ-max ℓ ℓ') ℓ'
Ob (c / x) = Σ (Ob c) λ a → Hom c a x
Hom (c / x) (A , f) (B , g) = Hom c A B

open IsCategory {{...}}

instance
  sliceCat : ∀ {ℓ} {ℓ'} {𝓒 : Category ℓ ℓ'} {X : Ob 𝓒} {{ _ : IsCategory 𝓒 }} → IsCategory (𝓒 / X)
  IsCategory.Id (sliceCat {{𝓒}}) = Id {{ 𝓒 }}
  IsCategory._∘_ (sliceCat {{𝓒}}) = _∘_ {{ 𝓒 }}

{-# OPTIONS --cubical --cumulativity #-}
module Categories.Groupoid where

open import Foundations.Prelude

open import Categories.Category

open IsCategory {{...}}

-- A strict groupoid. i.e. f ∘ f⁻¹ ≡ id
record Groupoid {ℓ} {ℓ'} (𝓖 : Category ℓ ℓ') {{𝓒cat : IsCategory 𝓖}} : Type (ℓ-max ℓ ℓ') where

  open Category 𝓖

  field
    _⁻¹  : ∀ {A B} → Hom A B → Hom B A
    sec  : ∀ {A B} {f : Hom A B} → Path {ℓ'} (Hom B B) (f ∘ (f ⁻¹)) Id
    ret  : ∀ {A B} {f : Hom A B} → Path {ℓ'} (Hom A A) Id           ((f ⁻¹) ∘ f)

{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Bicategory where


open import Foundations.Prelude

open import Categories.Category.Enriched
open Enriched renaming (Ob to EOb ; Hom to EHom)
open import Categories.Category
open Category
open import Categories.Functor
open import Categories.Diagram.Two

record IsBicategory {ℓ} {ℓ'} (𝓒 : Enriched (Category ℓ ℓ')) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    {{eIsCat}} : ∀ {x y}   → IsCategory (𝓒 .EHom x y)
    Id         : ∀ {x}     → 𝓒 .EHom x x .Ob
    _∘_        : ∀ {x y z} → Functor ({!𝓒 .EHom y z!} × {!𝓒 .EHom x y!}) (𝓒 .EHom x z)

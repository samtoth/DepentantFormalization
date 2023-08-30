{-# OPTIONS --cubical --cumulativity  #-}
module Categories.Category.Bicategory where


open import Foundations.Prelude

open import Categories.Category.Enriched
open Enriched renaming (Ob to EOb ; Hom to EHom)
open import Categories.Category
open Category
open import Categories.Functor
open import Categories.Diagram.Two
open import Categories.CATS

record IsBicategory {ℓ} {ℓ'} {ℓ''} (𝓒 : Enriched {ℓ} (Category ℓ' ℓ'')) : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
  field
    {{eIsCat}} : ∀ {x y}   → IsCategory (𝓒 .EHom x y)
    Id         : ∀ {x}     → 𝓒 .EHom x x .Ob
    Comp       : ∀ {x y z} → Functor (𝓒 .EHom y z × 𝓒 .EHom x y) (𝓒 .EHom x z)


module Ops {ℓ} {ℓ'} {ℓ''} {E𝓒 : Enriched {ℓ} (Category ℓ' ℓ'')} {{_ : IsBicategory E𝓒}} where


  _↦_ : (_ _ : E𝓒 .EOb) → Type ℓ'
  x ↦ y = E𝓒 .EHom x y .Ob

  _⇒_ : {x y : E𝓒 .EOb} → (_ _ : x ↦ y) → Type ℓ''
  f ⇒ g = E𝓒 .EHom _ _ .Hom f g

  open IsBicategory {{...}}

  _∘_ :  {x y z : E𝓒 .EOb} → y ↦ z → x ↦ y → x ↦ z
  f ∘ g = Comp .Functor.F0 (f , g)

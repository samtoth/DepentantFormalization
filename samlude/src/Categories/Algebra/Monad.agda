{-# OPTIONS --cubical --cumulativity  #-}
module Categories.Algebra.Monad where

open import Foundations.Prelude

open import Categories.Category.Base
open import Categories.Category.Enriched
open import Categories.Category.Bicategory
open import Categories.Functor
open Functor

module _ {ℓ} {ℓ'} {ℓ''} (𝓒 : Enriched {ℓ} {ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')} (Category ℓ' ℓ'')) ⦃ 𝓒Bi : IsBicategory 𝓒 ⦄ where

  open Enriched 𝓒
  open IsBicategory 𝓒Bi
  open Ops ⦃ 𝓒Bi ⦄

  record Monad : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
    field
      {x} : Ob
      F   : (x ↦ x)
      μ   : (F ∘ F) ⇒ F
      η   : Id      ⇒ F


{-# OPTIONS --cubical --cumulativity  #-}
module Categories.Algebra.Monad where

open import Foundations.Prelude

open import Categories.Category.Base
open import Categories.Category.Enriched
open import Categories.Category.Bicategory
open import Categories.Functor
open import Categories.FUNCTORS
open Functor

module _ {ℓ} {ℓ'} {ℓ''} (𝓒 : Enriched {ℓ} {ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')} (Category ℓ' ℓ'')) ⦃ 𝓒Bi : IsBicategory 𝓒 ⦄ where

  open Enriched 𝓒
  open IsBicategory 𝓒Bi
  open Ops ⦃ 𝓒Bi ⦄

  record Monad {x} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) where
    field
      F   : (x ↦ x)
      μ   : (F ∘ F) ⇒ F
      η   : Id      ⇒ F

  open Monad

  MonadHom : ∀ {x} (M T : Monad {x}) → Type ℓ''
  MonadHom M T = M .F ⇒ T .F


  MONAD : ∀ {x : Ob} → Category (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) ℓ''
  MONAD {x} = Cat (Monad {x}) MonadHom


  instance
    MONADisCat : ∀ {x} → IsCategory (MONAD {x})
    IsCategory.Id (MONADisCat {x}) {a} = cId
      where open IsCategory (eIsCat {x} {x}) renaming (Id to cId)
    IsCategory._∘_ (MONADisCat {x}) f g = Hom x x [ f ∘ g ]

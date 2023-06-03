{-# OPTIONS --cubical --cumulativity --allow-unsolved-metas #-}
module Categories.CATS where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Functor
open import Categories.TYPE

private
  variable
    ℓ ℓ' : Level

CATS : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-suc (ℓ-max ℓ ℓ'))
Category.Ob (CATS {ℓ} {ℓ'}) = Category ℓ ℓ'
Category.Hom CATS = Functor

open Functor {{...}}

module _ {ℓ : Level} {ℓ' : Level} where

  open IsCategory {{...}}

  instance
    CATSisCat : IsCategory (CATS {ℓ} {ℓ'})
    Functor.F0 (CATSisCat .Id) = Id
    Functor.F1 (CATSisCat .Id) = Id
    Functor.F0 ((CATSisCat ._∘_) F G) = F .F0 ∘ G .F0
    Functor.F1 ((CATSisCat ._∘_) F G) = F .F1 ∘ G .F1

  open import Categories.Diagram.Two
  open import Categories.Diagram.Zero
  open import Categories.Diagram.Base

  open Category

  open Limit

  instance
    CATSHasProducts : HasProducts CATS
    Ob (Cone.apex (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓}))) = 𝓒 .Ob × 𝓓 .Ob
    Hom (Cone.apex (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓}))) cd c'd' = 𝓒 .Hom (π₁ cd) (π₁ c'd') × 𝓓 .Hom (π₂ cd) (π₂ c'd')

    Functor.F0 (Cone.arrows (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓})) 𝟎) = π₁
    Functor.F1 (Cone.arrows (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓})) 𝟎) α = π₁ α

    Functor.F0 (Cone.arrows (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓})) 𝟏) = π₂
    Functor.F1 (Cone.arrows (HasLimit.lim (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓})) 𝟏) α = π₂ α

    Functor.F0 (HasLimit.lim-initial (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓}) x) a = {!!}
    Functor.F1 (HasLimit.lim-initial (HasProducts.hasLimit CATSHasProducts {𝓒} {𝓓}) x) = {!!}

    CATSHasLimits : ∀ {𝓙} {𝓓 : Functor 𝓙 CATS} → HasLimit 𝓓
    CATSHasLimits = {!!}

    CATSTerminal : Terminal CATS
    CATSTerminal = record {}

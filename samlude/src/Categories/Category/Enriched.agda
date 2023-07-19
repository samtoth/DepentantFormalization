{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Enriched where


open import Foundations.Prelude

record Enriched (ℓ : Level) {ℓ'} (E : Type ℓ') : Type (ℓ-max (ℓ-suc ℓ) ℓ') where
  constructor ECat
  field
    Ob  : Type ℓ
    Hom : Ob → Ob → E


module _ where
  open import Categories.TYPE
  open import Categories.Functor

  open Enriched

  instance
    EFun : ∀ {ℓ ℓ'} → Functor (TYPE ℓ') (TYPE (ℓ-max (ℓ-suc ℓ) ℓ'))
    Functor.F0 (EFun {ℓ}) = Enriched ℓ
    Functor.F1 EFun f e = ECat (e .Ob) λ a b → f (e .Hom a b)

open import Categories.Category

forget : ∀ {ℓ} {ℓ'} {E : Type ℓ'} {repr : E → Type ℓ'} → Enriched ℓ E → Category ℓ ℓ'
forget {repr  = repr} (ECat Ob Hom) = Cat Ob (λ x y → repr (Hom x y))

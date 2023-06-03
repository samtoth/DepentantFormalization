{-# OPTIONS --cubical --cumulativity #-}
module Categories.Functor.HomFunctor where

open import Foundations.Prelude

open import Categories.Category

module Hom {ℓ} {ℓ'} (𝓒 : Category ℓ (ℓ-max ℓ ℓ')) ⦃ 𝓒cat : IsCategory 𝓒 ⦄ where

  open import Categories.Functor.Base
  open import Categories.Diagram.Two

  open import Categories.TYPE
  open import Categories.CATS

  open Category 𝓒
  open IsCategory 𝓒cat

  Hom[-,-] : Functor ((𝓒 ^op)  × 𝓒 ) (TYPE {ℓ-max ℓ ℓ'})
  Functor.F0 Hom[-,-] (x , y) = Hom x y
  Functor.F1 Hom[-,-] (sym f , g) h = g ∘ (h ∘ f)


  Hom[_,-] : Ob → Functor 𝓒 (TYPE {ℓ-max ℓ ℓ'})
  Functor.F0 Hom[ x ,-] y = Hom x y
  Functor.F1 Hom[ x ,-] f g = f ∘ g

  open import Categories.NaturalTransformation renaming (NatTrans to _=>_)
  open import Categories.Functor
  open Functor

  yoneda : ∀ {c : Ob} {F : Functor 𝓒 TYPE} → Hom[ c ,-] => F → F .F0 c
  yoneda {c} α = α c Id

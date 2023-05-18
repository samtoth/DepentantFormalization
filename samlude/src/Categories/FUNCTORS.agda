{-# OPTIONS --cubical --cumulativity #-}
module Categories.FUNCTORS where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

open Category {{...}}

F[_,_] : ∀ {ℓC ℓC' ℓD ℓD'} → Category {ℓC} {ℓC'} → Category {ℓD} {ℓD'} → Category {ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')} {ℓ-suc (ℓ-max ℓC ℓD')}
F[ C , D ] .Ob  = Functor C D
F[ C , D ] .Hom = NatTrans

open IsCategory {{...}}

instance
  FCat : ∀ {ℓC ℓC' ℓD ℓD'} {C : Category {ℓC} {ℓC'}} {D : Category {ℓD} {ℓD'}} ⦃ _ : IsCategory D ⦄ → IsCategory F[ C , D ]
  IsCategory.Id FCat = λ a → Id
  IsCategory._∘_ FCat = λ α β → λ a → α a ∘ β a

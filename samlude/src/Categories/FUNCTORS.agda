{-# OPTIONS --cubical --cumulativity #-}
module Categories.FUNCTORS where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

open Category {{...}}

F[_,_] : ∀ {ℓC ℓC' ℓD ℓD'} → Category ℓC ℓC' → Category ℓD ℓD' → Category (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) (ℓ-suc (ℓ-max ℓC ℓD'))
F[ C , D ] .Ob  = Functor C D
F[ C , D ] .Hom = NatTrans

open IsCategory


instance
  FCat : ∀ {ℓC ℓC' ℓD ℓD'} {𝓒 : Category ℓC ℓC'} {𝓓 : Category ℓD ℓD'} ⦃ dcat : IsCategory 𝓓 ⦄ → IsCategory F[ 𝓒 , 𝓓 ]
  IsCategory.Id (FCat ⦃ dcat ⦄) = λ a → Id dcat
  IsCategory._∘_ (FCat {𝓓 =  𝓓 }) = λ α β → λ a → 𝓓 [ α a ∘ β a ]

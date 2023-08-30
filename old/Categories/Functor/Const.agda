{-# OPTIONS --cubical #-}
module Categories.Functor.Const where

open import Categories.Category
open import Categories.Functor.Base

module _ {ℓ} {ℓ'} {𝓒 𝓓 : Category ℓ ℓ'} ⦃ 𝓓Cat : IsCategory 𝓓 ⦄ where

  open Category

  Const : 𝓓 .Ob → Functor 𝓒 𝓓
  Const x = record { F0 = λ _ → x ; F1 = λ f → Id }
    where open IsCategory 𝓓Cat

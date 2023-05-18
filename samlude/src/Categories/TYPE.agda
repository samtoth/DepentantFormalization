{-# OPTIONS --cubical --cumulativity #-}
module Categories.TYPE where

open import Foundations.Prelude
open import Categories.Category.Base

private
  variable
    ℓ ℓ' : Level

TYPE : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Category.Ob (TYPE {ℓ}) = Type ℓ
Category.Hom TYPE = λ a b → a → b

open IsCategory ⦃...⦄

instance
  TYPEcat : IsCategory TYPE
  TYPEcat .Id = λ x → x
  TYPEcat ._∘_ = λ f g x → f (g x)

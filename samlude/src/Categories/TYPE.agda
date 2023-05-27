{-# OPTIONS --cubical --cumulativity #-}
module Categories.TYPE where

open import Foundations.Prelude
open import Categories.Category.Base


TYPE : {ℓ ℓ' : Level} → Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Category.Ob (TYPE {ℓ}) = Type ℓ
Category.Hom TYPE = λ a b → a → b

open IsCategory ⦃...⦄

module _ {ℓ ℓ' : Level} where
  instance
    TYPEcat : IsCategory (TYPE {ℓ} {ℓ'})
    TYPEcat .Id = λ x → x
    TYPEcat ._∘_ = λ f g x → f (g x)


  open import Categories.Diagram.Two

  open import Categories.Diagram.Base

  open Limit
  open Cone

  instance
    TYPEProducts : HasProducts TYPE
    Limit.Cone.apex (Limit.HasLimit.lim (HasProducts.hasLimit TYPEProducts {A} {B})) = Σ A λ _ → B
    Limit.Cone.arrows (Limit.HasLimit.lim (HasProducts.hasLimit TYPEProducts {A} {B})) 𝟎 (a , _) = a
    Limit.Cone.arrows (Limit.HasLimit.lim (HasProducts.hasLimit TYPEProducts {A} {B})) 𝟏 (_ , b) = b
    Limit.HasLimit.lim-initial (HasProducts.hasLimit TYPEProducts {A} {B}) cone A×B = cone .arrows 𝟎 A×B , cone .arrows 𝟏 A×B

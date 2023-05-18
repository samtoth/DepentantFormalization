{-# OPTIONS --cubical --cumulativity #-}
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

open IsCategory {{...}}
open Functor {{...}}

instance
  CATSisCat : IsCategory CATS
  CATSisCat .Id = record { F0 = Id ; F1 = Id }
  CATSisCat ._∘_ = λ f g → record { F0 = f .F0 ∘ g .F0 ; F1 =  f .F1 ∘ g .F1 }

{-# OPTIONS --cubical --cumulativity #-}
module Categories.Negation where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Diagram.Zero
open import Categories.Diagram.Two

open import Categories.CartesianClosed

module _ {ℓ} {𝓒 : Category ℓ ℓ} {{_ : IsCategory 𝓒}} {{_ : HasProducts 𝓒}} {{_  : CC 𝓒}} {{_ : Initial 𝓒}} where

  open Category 𝓒
  open Initial {{...}}

  open CC {{...}}

  ¬_ : Ob → Ob
  ¬ X = [ X , ⊥ ]

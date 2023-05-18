{-# OPTIONS --cubical --cumulativity #-}
module Categories.Diagram.Terminal where

open import Foundations.Prelude
open import Categories.Category
open import Categories.CATS
open import Categories.Diagram.Base

private
  variable
    ℓ ℓ' : Level

data ∅ {ℓ} : Type ℓ where


⊤cat : Category ℓ ℓ'
⊤cat = Cat ∅ λ ()

module _ {𝓒 : Category ℓ ℓ'} ⦃ ccat : IsCategory 𝓒 ⦄ where

  open Category 𝓒
  open IsCategory ccat

  open HasLimit {{...}}
  open Cone

  ⊤ : {F : CATS [ ⊤cat , 𝓒 ]} ⦃ _ : HasLimit F ⦄ → Ob
  ⊤ = lim .apex

  ! : {F : CATS [ ⊤cat , 𝓒 ]} ⦃ _ : HasLimit F ⦄ {x : Ob} → Hom x ⊤
  ! {F} {{r}} {x = x} = lim-initial (record { apex = x ; arrows = λ () })

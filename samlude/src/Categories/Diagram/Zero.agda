{-# OPTIONS --cubical --cumulativity #-}
module Categories.Diagram.Zero where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Diagram.Base

private
  variable
    ℓ ℓ' : Level

  data Empty {ℓ} : Type ℓ where


  ⊥cat : Category ℓ ℓ'
  ⊥cat = Cat Empty λ _ _ → Empty

record Terminal (𝓒 : Category ℓ ℓ') ⦃ ccat : IsCategory 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Category 𝓒
  open IsCategory ccat

  open Limit
  open HasLimit {{...}}
  open Cone

  D : Diagram ⊥cat 𝓒
  D = record { F0 = λ () ; F1 = λ () }

  field
    {{haslim}} : HasLimit D

  ⊤ :  Ob
  ⊤ = lim .apex

  ! : {x : Ob} → Hom x ⊤
  ! {x = x} = lim-initial (record { apex = x ; arrows = λ () })

  get : ∀ {x : Ob} → Hom ⊤ x → Ob
  get {x} _ = x



record Initial (𝓒 : Category ℓ ℓ') ⦃ ccat : IsCategory 𝓒 ⦄  : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Category (𝓒 ^op)
  open IsCategory (catOp ⦃ ccat ⦄)

  open Limit {𝓒 = 𝓒 ^op}
  open HasLimit {{...}}
  open Cone


  D : Diagram ⊥cat (𝓒 ^op)
  D = record { F0 = λ () ; F1 = λ () }


  field
    {{hascolim}} : HasLimit D

  ⊥ :  Ob
  ⊥ = apex lim

  ¡ :  {x : Ob} → Hom x ⊥
  ¡ {x = x} = lim-initial (record { apex = x ; arrows = λ () })

open Terminal {{...}}
open Initial {{...}}


record Zero {𝓒 : Category ℓ ℓ'} ⦃ ccat : IsCategory 𝓒 ⦄ ⦃ _ : Terminal 𝓒 ⦄ ⦃ _ : Initial 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ⊥⊤ : ⊥ ≡ ⊤

  open Category 𝓒

  ∅ : Ob
  ∅ = ⊤

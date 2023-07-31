{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Categories.TYPE where

open import Foundations.Prelude
open import Categories.Category.Base
open import Categories.Category.Lift
open import Categories.Functor


TYPE : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Category.Ob (TYPE ℓ) = Type ℓ
Category.Hom (TYPE _) = λ a b → a → b

open IsCategory ⦃...⦄

module _ {ℓ : Level} where
  instance
    TYPEcat : IsCategory (TYPE ℓ)
    TYPEcat .Id = λ x → x
    TYPEcat ._∘_ f g = λ x → f (g x)


  open import Categories.Diagram.Two
  open import Categories.Diagram.Zero

  open import Categories.Diagram.Base

  open Limit
  open Cone


  instance


    open Category
    open Functor

    TYPEComplete : ∀ {𝓙 : Category ℓ ℓ} {D : Diagram (LiftC 𝓙 (ℓ-suc ℓ) ℓ) (TYPE ℓ)} → HasLimit D
    apex (HasLimit.lim (TYPEComplete {𝓙} {D}))  = (j : 𝓙 .Ob) → D .F0 (lift j)
    arrows (HasLimit.lim TYPEComplete) (lift j) = λ f → f j
    HasLimit.lim-initial (TYPEComplete {𝓙}) record { apex = Apex ; arrows = arr } = λ a j → arr (lift j) a

    TYPECoComplete : ∀ {𝓙 : Category ℓ ℓ} {D : Diagram (LiftC 𝓙 (ℓ-suc ℓ) (ℓ-suc ℓ)) ((TYPE ℓ) ^op)} → HasLimit D
    apex (HasLimit.lim (TYPECoComplete {𝓙} {D})) = {!!}
    arrows (HasLimit.lim TYPECoComplete) j = sym {!!}
    HasLimit.lim-initial TYPECoComplete = {!!}

    TYPEInitial : Initial (TYPE ℓ)
    Initial.hascolim TYPEInitial = {!!}

    TYPETerminal : Terminal (TYPE ℓ)
    Terminal.haslim TYPETerminal = {!!}

    TYPEProducts : HasProducts (TYPE ℓ)
    HasProducts.hasLimit TYPEProducts = {!TYPEComplete!}


    TYPECoProducts : HasCoproducts (TYPE ℓ)
    HasCoproducts.hasColim TYPECoProducts = {!TYPECoComplete!}

  open HasProducts {{...}}

  _,,_ : ∀ {A B : Ob (TYPE ℓ)} → A → B → A × B
  _,,_ a = ×⟨ (λ _ → a) , (λ b  → b) ⟩

  open import Categories.CartesianClosed

  instance
    TYPECC : CC (TYPE ℓ)
    CC.[_,_] TYPECC = {!!}
    CC.[un]curry TYPECC = {!!}

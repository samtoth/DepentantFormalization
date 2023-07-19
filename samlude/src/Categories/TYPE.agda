{-# OPTIONS --cubical --cumulativity --allow-unsolved-metas #-}
module Categories.TYPE where

open import Foundations.Prelude
open import Categories.Category.Base
open import Categories.Category.Lift
open import Categories.Functor


TYPE : (ℓ : Level) → Category (ℓ-suc ℓ) (ℓ-suc ℓ)
Category.Ob (TYPE ℓ) = Type ℓ
Category.Hom (TYPE _) = λ a b → a → b

open IsCategory ⦃...⦄

module _ {ℓ : Level} where
  instance
    TYPEcat : IsCategory (TYPE ℓ)
    TYPEcat .Id = λ x → x
    TYPEcat ._∘_ = λ f g x → f (g x)


  open import Categories.Diagram.Two
  open import Categories.Diagram.Zero

  open import Categories.Diagram.Base

  open Limit
  open Cone


  instance


    open Category
    open Functor

    TYPEComplete : ∀ {𝓙 : Category ℓ ℓ} {D : Diagram (Lift 𝓙) (TYPE ℓ)} → HasLimit D
    apex (HasLimit.lim (TYPEComplete {𝓙} {D}))  = (j : 𝓙 .Ob) → D .F0 j
    arrows (HasLimit.lim TYPEComplete) j f = f j
    HasLimit.lim-initial (TYPEComplete {𝓙}) record { apex = apex ; arrows = arr } ap = λ j → arr (lift {𝓒 = 𝓙} .F0 j) ap

    TYPECoComplete : ∀ {𝓙 : Category ℓ ℓ} {D : Diagram (Lift 𝓙) (TYPE ℓ ^op)} → HasLimit D
    apex (HasLimit.lim (TYPECoComplete {𝓙} {D})) = {!!}
    arrows (HasLimit.lim TYPECoComplete) j = sym {!!}
    HasLimit.lim-initial TYPECoComplete = {!!}

    TYPEInitial : Initial (TYPE ℓ)
    Initial.hascolim TYPEInitial = TYPECoComplete

    TYPETerminal : Terminal (TYPE ℓ)
    Terminal.haslim TYPETerminal = TYPEComplete

    TYPEProducts : HasProducts (TYPE ℓ)
    HasProducts.hasLimit TYPEProducts = {!TYPEComplete!}


    TYPECoProducts : HasCoproducts (TYPE ℓ)
    HasCoproducts.hasColim TYPECoProducts = {!TYPECoComplete!}

  open import Categories.CartesianClosed

  instance
    TYPECC : CC {ℓ-suc ℓ} (TYPE ℓ)
    CC.[_,_] TYPECC = λ A B → A → B
    CC.[un]curry TYPECC = {!!}

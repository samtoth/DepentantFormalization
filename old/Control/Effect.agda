{-# OPTIONS --cubical --cumulativity #-}
module Control.Effect where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Functor
open import Categories.Over

open Category
open Functor

open import Categories.Diagram.Two

module _ {ℓ} {ℓ'} {𝓒 : Category ℓ ℓ'} {Effects : Category ℓ ℓ'} (J : Functor Effects 𝓒 ) where
  Effect : Type
  Effect = ∀ (a : Ob 𝓒) → Functor ((Lift Effects) × (Effects / a)) 𝓒

  data EFFECT : Type where
    _⊢_ : Effect → Type → EFFECT


  data Eff (A : Type) : Effects → (A → Effects) → Type where
    retE  : ∀  {eout} → (x : A) → Eff A (eout x) eout

    bindE : ∀ {B} {ein} {eout} {eout'} → Eff B ein eout → ((x : B) → Eff A (eout x) eout') → Eff A ein eout'

    -- callE : ∀ {E : Effect} (i : E ⊢ (Resᵢ ∈ esᵢ)) (e : E A Resᵢ Resₒ) →
    --         Eff M A esᵢ (λ x → updateResTy x i e)

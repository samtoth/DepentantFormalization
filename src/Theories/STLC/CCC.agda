open import Cat.Prelude
open import Cat.Strict
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Diagram.Exponential

module Theories.STLC.CCC {o} {ℓ} (𝓒 : Precategory o ℓ)
       (𝓒-term : Terminal 𝓒) (𝓒-prod : has-products 𝓒) (𝓒cc : Cartesian-closed 𝓒 𝓒-prod 𝓒-term) where

-- This module constructs the equivalence between the STLC model (sCwF) and CCCs

open import Theories.STLC.Model
open Functor
open import Cat.Functor.Bifunctor
open import Cat.Functor.Naturality
open import Cat.Reasoning 𝓒

open Binary-products 𝓒 𝓒-prod

{-# TERMINATING #-}
CCC-model : STLC
CCC-model .STLC.𝓒 = 𝓒
CCC-model .STLC.𝓒-term = 𝓒-term
CCC-model .STLC.Ty = Ob
CCC-model .STLC.𝕋 A .F₀ B = el (Hom B A) (Hom-set B A)
CCC-model .STLC.𝕋 A .F₁ F G = G ∘ F
CCC-model .STLC.𝕋 A .F-id = funext idr
CCC-model .STLC.𝕋 A .F-∘ f g = funext λ x → assoc x g f
CCC-model .STLC.extend t = Right ×-functor t
CCC-model .STLC.extension Γ A = to-natural-iso  the-iso where
  the-iso : make-natural-iso _ _
  the-iso .make-natural-iso.eta Δ (α , β) = ⟨ β , α ⟩
  the-iso .make-natural-iso.inv Δ α = (π₂ ∘ α , π₁ ∘ α)
  the-iso .make-natural-iso.eta∘inv F = funext λ x → ⟨ π₁ ∘ x , π₂ ∘ x ⟩ ≡⟨ sym (⟨⟩∘ x) ⟩
                                                      ⟨ π₁ , π₂ ⟩ ∘ x    ≡⟨ ⟨⟩-η ⟩∘⟨refl ⟩
                                                      id ∘ x             ≡⟨ idl x ⟩
                                                      x ∎
  the-iso .make-natural-iso.inv∘eta F = funext λ _ → ap₂ _,_ π₂∘factor π₁∘factor where
                                          open Product (𝓒-prod A Γ)
  the-iso .make-natural-iso.natural Δ Σ α = funext λ _ → ⟨⟩∘ α 
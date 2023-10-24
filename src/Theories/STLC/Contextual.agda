{-# OPTIONS --allow-unsolved-metas #-}
module Theories.STLC.Contextual where

open import 1Lab.Prelude

open import Theories.STLC.Model


Contextual : ∀ {o ℓ} → STLC {o} {ℓ} → Type (o ⊔ lsuc ℓ)
Contextual {o} {ℓ} x = ∀ (P : Ctx → Type ℓ)
                       → P ε → (∀ {Γ} {A} → P Γ → P (Γ ⊕ A))
                       → ∀ Γ → P Γ 
    where open STLC x
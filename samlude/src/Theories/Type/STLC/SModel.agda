{-# OPTIONS --cubical #-}
module Theories.Type.STLC.SModel where

open import Foundations.Prelude

open import Theories.Type.STLC.Syntax

open import Data.Bool renaming (Bool to 𝔹)

open import Categories.Category
open import Categories.TYPE
open IsCategory (TYPEcat {ℓ-zero})
open import Categories.Functor
open Functor
open import Categories.Diagram.Zero
open import Categories.Diagram.Two
open Terminal {{... }}
open HasProducts {{...}}

⟦_⟧ₜ : Ty → Type
⟦ Bool ⟧ₜ = 𝔹
⟦ A ⇒ B ⟧ₜ = ⟦ A ⟧ₜ → ⟦ B ⟧ₜ

----------------------------------------------------------
-------  interpretations of contexts and terms  ----------
----------------------------------------------------------

⟦_⟧ctx : Ctx → Type
⟦ ε ⟧ctx = ⊤
⟦ Γ , τ ⟧ctx = ⟦ Γ ⟧ctx × ⟦ τ ⟧ₜ


⟦_⟧ : ∀ {Γ A} → Term Γ A → ⟦ Γ ⟧ctx → ⟦ A ⟧ₜ
⟦_⟧ₐ : ∀ {Γ Δ} → Subst Γ Δ → ⟦ Γ ⟧ctx → ⟦ Δ ⟧ctx

⟦ SId ⟧ₐ = Id
⟦ SComp γ δ ⟧ₐ = ⟦ γ ⟧ₐ ∘ ⟦ δ ⟧ₐ
⟦ lid {γ = γ} i ⟧ₐ = ⟦ γ ⟧ₐ
⟦ rid {γ = γ} i ⟧ₐ = ⟦ γ ⟧ₐ
⟦ assoc  {γ = γ} {δ = δ} {ψ = ψ} i ⟧ₐ = ⟦ γ ⟧ₐ ∘ (⟦ δ  ⟧ₐ ∘ ⟦ ψ ⟧ₐ)
⟦ ⟨⟩ ⟧ₐ = !
⟦ ⟨⟩! γ i ⟧ₐ = refl i
⟦ ⟨ γ , x ⟩ ⟧ₐ = ×⟨ ⟦ γ ⟧ₐ , ⟦ x [ γ ] ⟧  ⟩
⟦ p ⟧ₐ = π₁
⟦ p∘⟨-,-⟩ i ⟧ₐ = {!π₁∘× {{TYPEcat}} {{TYPEProducts}} {{TYPEProperProd}} i!}
⟦ set P Q i j ⟧ₐ = {!!}

---------------------------------------------------------

⟦ q ⟧ = π₂

⟦ t [ γ ] ⟧ = ⟦ t ⟧ ∘ ⟦ γ ⟧ₐ

⟦ [][] {a = a} {γ = γ} {δ = δ} i ⟧ Γ = ⟦ a ⟧ (⟦ γ ⟧ₐ (⟦ δ ⟧ₐ Γ))
⟦ [Id] {a = a} i ⟧ = ⟦ a ⟧
⟦ q[⟨-,-⟩] i ⟧ Γ = {!π₂∘×!}

⟦ lam x ⟧ Γ = ⟦ x ⟧ ∘ ×⟨ (λ _ → Γ) , Id ⟩

⟦ app f x ⟧ Γ = (⟦ f ⟧ Γ) (⟦ x ⟧ Γ)

⟦ β f x i ⟧ = λ Γ → ⟦ f ⟧ {!×⟨ Γ , ? ⟩!}
--                             boundary:    (×⟨ (λ _ → Γ) , (λ x₁ → x₁) ⟩ (⟦ x ⟧ Γ))
                                         -- (×⟨ (λ x₁ → x₁) , (λ x₁ → ⟦ x ⟧ x₁) ⟩ Γ)

⟦ η x i ⟧ = λ Γ a → ⟦ x ⟧ {! π₁∘×⟨constΓ⟩≡constΓ i !} {! π₂∘×⟨id⟩≡id i !}

⟦ true ⟧ = λ _ → true
⟦ false ⟧ = λ _ → false
⟦ if x then t else f ⟧ Γ with ⟦ x ⟧ Γ
... | true  = ⟦ t ⟧ Γ
... | false = ⟦ f ⟧ Γ
⟦ ite-true {a = a}  i ⟧ = ⟦ a ⟧
⟦ ite-false {a' = a'} i ⟧ = ⟦ a' ⟧

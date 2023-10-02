module Theories.STLC.CCC where

-- This module constructs the equivalence between the STLC model (sCwF) and CCCs

open import Cat.Prelude
open import Cat.Diagram.Product
open import Cat.CartesianClosed.Base
open import Theories.STLC.Model

open Functor

data Ctx {ℓ} (ty : Type ℓ) : Type ℓ where
    ε : Ctx ty
    _,_ : Ctx ty → ty → Ctx ty


data Els {ℓ₁ ℓ₂} {ty : Type ℓ₁} (el : ty → Type ℓ₂) : (Γ : Ctx ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : Els el ε
  _⊕_ : {Γ : Ctx ty} {A : ty} → Els el Γ → el A → Els el (Γ , A)

Sub : ∀ {o ℓ} {ty : Type o} (T : Ctx ty → ty → Type ℓ) (A B : Ctx ty) → Type (o ⊔ ℓ)
Sub T Γ Δ = Els (T Γ) Δ

STLC→CCC : ∀ {o ℓ} → STLC {o} {ℓ} → Σ[ 𝓒 ∈ Precategory o (o ⊔ ℓ) ] Σ[ cart ∈ (∀ A B → Product 𝓒 A B) ] (is-cc 𝓒 cart)
STLC→CCC {o} {ℓ} S = cat , cart , cc
    where module S = STLC S
          
          module SC = Precategory S.𝓒

          toCtx : Ctx S.Ty → S.𝓒 .Precategory.Ob
          toCtx ε = S.ε
          toCtx (Γ , A) = toCtx Γ S.⊕ A 

          toSub : ∀ {Γ Δ} → Sub (λ Γ A → ∣ S.𝕋 A .F₀ (toCtx Γ) ∣) Γ Δ → S.Sub (toCtx Γ) (toCtx Δ)
          toSub ! = S.⟨⟩ _
          toSub {Γ} {Δ , A} (γ ⊕ x) = S.⟨ toSub {Γ} {Δ} γ  , x ⟩

          T = λ Γ A → ∣ S.𝕋 A .F₀ (toCtx Γ) ∣

          wk1 : ∀ {Γ Δ A} → Sub T Γ Δ → Sub T (Γ , A) Δ
          wk1 ! = !
          wk1 {Γ} {Δ , B} {A} (γ ⊕ x) = wk1 {Γ} {Δ} {A} γ ⊕ (x S.[ S.p SC.id ])
             
          wk2 : ∀ {Γ Δ A} → Sub T Γ Δ → Sub T (Γ , A) (Δ , A)
          wk2 {Γ} {Δ} {A} γ = (wk1 {Γ} {Δ} {A} γ) ⊕ S.q SC.id

          idsub : (Γ : Ctx S.Ty) → Sub T Γ Γ
          idsub ε = !
          idsub (Γ , A) = wk2 {Γ} {Γ} {A} (idsub Γ)

          toSubId : ∀ {Γ} → toSub {Γ} {Γ} (idsub Γ) ≡ SC.id {toCtx Γ}
          toSubId {ε} = S.⟨⟩! SC.id
          toSubId {Γ , x} = {!   !}

          sub∘ : ∀ {Γ Δ Σ} → Sub T Δ Σ → Sub T Γ Δ → Sub T Γ Σ
          sub∘ ! δ = !
          sub∘ {Γ} {Δ} {Σ , A} (γ ⊕ x) δ = sub∘ {Γ} γ δ ⊕ (x S.[ toSub {Γ} δ ])

          idr : ∀ {Γ Δ} → (γ : Sub T Γ Δ) → sub∘ {Γ} {Γ} {Δ} γ (idsub Γ) ≡ γ
          idr ! = refl
          idr {Γ} {Δ , A} (γ ⊕ x) = λ i → (idr {Γ} {Δ} γ i) ⊕ ((λ j → x S.[ toSubId {Γ} j ]) ∙ (x S.[Id])) i 


          cat : Precategory _ _
          cat .Precategory.Ob = Ctx (S.Ty)
          cat .Precategory.Hom = Sub (λ Γ A → ∣ S.𝕋 A .F₀ (toCtx Γ) ∣)
          cat .Precategory.Hom-set = {!   !}
          cat .Precategory.id = idsub _
          cat .Precategory._∘_ {Γ} {Δ} {Σ} γ δ = sub∘ {Γ} {Δ} {Σ} γ δ
          cat .Precategory.idr = idr
          cat .Precategory.idl = {!   !}
          cat .Precategory.assoc = {!   !}

          cart : ∀ A B → Product cat A B
          cart = {!   !}

          cc : is-cc cat cart
          cc = {!   !}      
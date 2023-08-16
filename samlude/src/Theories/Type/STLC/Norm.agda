{-# OPTIONS --cubical #-}
module Theories.Type.STLC.Norm where

open import Foundations.Prelude

open import Theories.Type.STLC.Syntax
open import Theories.Type.STLC.Vals

open import Categories.Category
open import Categories.Functor
open import Categories.TYPE

open Functor

-- Types are mapped to presheafs over the context



TyPS : Ty → Functor (Ctxs ^op) (TYPE ℓ-zero)
TyPS x = record { F0 = fOb x ; F1 = λ {(sym γ) → fHom x γ }}
  where
    fOb : Ty → Ctx → Type
    fOb Bool Γ = Val Nf Γ Bool
    fOb (A ⇒ B) Γ = ∀ {Δ} → Subst Δ Γ → TyPS A .F0 Δ → TyPS B .F0 Δ


    fHom : ∀ {Γ Δ : Ctx} → (A : Ty) → Subst Δ Γ → fOb A Γ → fOb A Δ
    fHom A SId = λ v → v
    fHom A (SComp γ δ) = TYPE ℓ-zero [ fHom A δ ∘ fHom A γ ]
    fHom A (lid {γ = γ} i) v = fHom A γ v
    fHom A (rid {γ = γ} i) v = fHom A γ v

    fHom A (assoc {γ = γ} {δ = δ} {ψ = ψ} i) v = fHom A ψ (fHom A δ (fHom A γ v))

    fHom {Δ = ε} A (⟨⟩ {.ε}) v = v

    fHom {Δ = Γ , x} Bool (⟨⟩ {.(Γ , x)}) v = wk (fHom Bool ⟨⟩ v)
    fHom {Δ = Γ , x} (A ⇒ B) (⟨⟩ {.(Γ , x)}) v = λ δ → v ⟨⟩

    fHom A (⟨⟩! γ i) v = {!!}

    fHom Bool ⟨ γ , x ⟩ (ne (app v v₁)) = {!n!}
    fHom Bool ⟨ γ , x ⟩ (ne q) = {!!}
    fHom Bool ⟨ γ , x ⟩ (ne (if v then v₁ else v₂)) = {!!}
    fHom Bool ⟨ γ , x ⟩ (wk v) = {!wk!}
    fHom Bool ⟨ γ , x ⟩ true = true
    fHom Bool ⟨ γ , x ⟩ false = false

    fHom (A ⇒ A₁) ⟨ γ , x ⟩ v = {!!}

    fHom A p v = {!!}
    fHom A (p∘⟨-,-⟩ i) v = {!!}
    fHom A (set p₁ q₁ i i₁) v = {!!}

-- F0 (TyPS Bool) Γ = Val Nf Γ Bool

-- F1 (TyPS Bool) (sym SId) v = v
-- F1 (TyPS Bool) (sym (SComp γ δ)) = (TYPE ℓ-zero) [ TyPS Bool .F1 (sym δ) ∘ TyPS Bool .F1 (sym γ) ]
-- F1 (TyPS Bool) (sym (lid i)) v = {!!}
-- F1 (TyPS Bool) (sym (rid i)) v = {!!}
-- F1 (TyPS Bool) (sym (assoc i)) v = {!!}
-- F1 (TyPS Bool) (sym ⟨⟩) v = {!!}
-- F1 (TyPS Bool) (sym (⟨⟩! γ i)) v = {!!}
-- F1 (TyPS Bool) (sym ⟨ γ , x ⟩) v = {!!}
-- F1 (TyPS Bool) (sym p) v = {!!}
-- F1 (TyPS Bool) (sym (p∘⟨-,-⟩ i)) v = {!!}
-- F1 (TyPS Bool) (sym (set p₁ q₁ i i₁)) v = {!!}

-- F0 (TyPS (A ⇒ B)) Γ = ∀ {Δ} → Subst Δ Γ → TyPS A .F0 Δ → TyPS B .F0 Δ
-- F1 (TyPS (A ⇒ B)) = {!!}


norm : Term Γ A → Val Nf Γ A
norm x = {!!}

module Theories.STLC.Norm  where

open import 1Lab.Prelude hiding (⌜_⌝ ; _<*>_)
open import Cat.Base
open import Cat.Functor.Base
open import Cat.Diagram.Initial
open _=>_
open Functor

open import Theories.STLC.HIITctx
open import Theories.STLC.Vals
open import Theories.STLC.Model
open import Theories.STLC.Ctxs
open import Cat.Displayed.Total

open Model

Tyₛ : Set lzero
Tyₛ = el Ty Ty-is-set

module Psh = Precategory (PSh lzero (Rens Tyₛ))

inclVar : Var Γ A → ∣ Term Γ A ∣ 
inclVar vz = ιvz
inclVar (vs v) = ιvsuc (inclVar v)

inclRen : R.Hom Δ Γ → ιSTLC Sub (Γ , Δ)
inclRen ! = ⟨⟩
inclRen (ρ ⊕ v) = ⟨ inclRen ρ , inclVar v ⟩

incWk1 : ∀ (ρ : Ren Γ Δ) → inclRen (wk1Ren {A = A} ρ) ≡ p (inclRen (wk2Ren ρ))
incWk1 ! = sym p⟨ _ , _ ⟩
incWk1 (ρ ⊕ x) = sym p⟨ _ , _ ⟩

incRenId : ∀ Γ → inclRen (idRen {Γ = Γ}) ≡ ιSTLC.Id
incRenId ε = ⟨⟩! _
incRenId (Γ , x) = {!   !}

Ren→Subs : Functor (Rens Tyₛ) Subs
Ren→Subs .F₀ = id
Ren→Subs .F₁ = inclRen
Ren→Subs .F-id = incRenId _
Ren→Subs .F-∘ f g = {!   !}

TmPs : Ty → Psh.Ob
TmPs A .F₀ Γ = Term Γ A
TmPs A .F₁ ρ t = t [ inclRen ρ ]
TmPs A .F-id = funext λ x →  ap (x [_]) (incRenId _) ∙ (x [Id])
TmPs A .F-∘ = {!   !}


⌜ValPs⌝ : (v : ValKind) → (A : Ty) → Psh.Hom (ValPs v A) (TmPs A)
⌜ValPs⌝ v A .η Γ val = ⌜ val ⌝ 
⌜ValPs⌝ v A .is-natural Γ Δ ρ = {!   !} 
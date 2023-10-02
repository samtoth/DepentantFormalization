module Theories.STLC.Norm where

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

-- First the naive normalisation function

ToNorm : STLC-Functor ιSTLC-model Model.NF
ToNorm = ιSTLC-is-initial .Initial.has⊥ (Model.NF , Model.NFLam , Model.NFBool) .is-contr.centre .Total-hom.hom

PresTy : ∀ (A) → ToNorm .STLC-Functor.Fty A ≡ A
PresTy 𝔹 = refl
PresTy (A ⇒ B) = ap₂ _⇒_ (PresTy A) (PresTy B)


PresCtx : ∀ (Γ) → ToNorm .STLC-Functor.F .F₀ Γ ≡ Γ
PresCtx (ε) = refl
PresCtx (Γ , x) = λ i → (PresCtx Γ i) , (PresTy x i)

toNorm : ∀ {Γ A} → ιSTLC Tm (Γ , A) → Val Nf Γ A
toNorm {Γ} {A} = transp (λ i → Val Nf (PresCtx Γ i) (PresTy A i)) i0 ∘ ToNorm .STLC-Functor.F𝕋 .η Γ

toNorm' : ∀ {Γ A} → ιSTLC Tm (Γ , A) → Val Nf (ToNorm .STLC-Functor.F .F₀ Γ) (ToNorm .STLC-Functor.Fty A)
toNorm' {Γ} {A} = ToNorm .STLC-Functor.F𝕋 .η Γ

nf' : ∀ {Γ A} → ιSTLC Tm (Γ , A) → ιSTLC Tm (_ , _)
nf' = ⌜_⌝ ∘ toNorm'

nf⁰ : ∀ {Γ A} → ιSTLC Tm (Γ , A) → ιSTLC Tm (Γ , A)
nf⁰ = ⌜_⌝ ∘ toNorm

test : ∀ {A B} {f : ιSTLC Tm (ε , A ⇒ B)} → nf⁰ {ε} (lam (app f)) ≡ nf⁰ f
test = {!  refl !}

idfun : ∀ {A} → ιSTLC Tm (Γ , A ⇒ A)
idfun = lam ιvz

_<*>_ : ιSTLC Tm (Γ , A ⇒ B) → ιSTLC Tm (Γ , A) → ιSTLC Tm (Γ , B)
f <*> x = app f [ ⟨ ιSTLC.Id , x ⟩ ]

infixl 25 _<*>_

lamapp : ∀ {A B} (f : ιSTLC Tm (ε , A ⇒ B)) → ιSTLC Tm (ε , A ⇒ B)
lamapp f = lam (app f)

and : ιSTLC Tm (Γ , (𝔹 ⇒ 𝔹 ⇒ 𝔹))
and = lam (elim𝔹 ιvz idfun (lam false))

testAnd : nf'  {Γ , 𝔹} (and <*> false <*> ιvz)  ≡ false
testAnd = refl

not : ιSTLC Tm (Γ , (𝔹 ⇒ 𝔹))
not = lam (elim𝔹 ιvz false true)

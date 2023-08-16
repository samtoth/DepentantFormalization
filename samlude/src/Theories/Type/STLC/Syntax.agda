{-# OPTIONS --cubical #-}
module Theories.Type.STLC.Syntax where

open import Foundations.Prelude

open import Data.Fin

open import Foundations.Decidable
open import Categories.TYPE
open import Categories.Negation {𝓒 = TYPE ℓ-zero}
open import Categories.Diagram.Zero
open import Categories.Diagram.Two

open Terminal {{...}}
open Initial {{...}}
open HasProducts {{...}}

data Ty : Type where
  Bool : Ty
  _⇒_  : Ty → Ty → Ty


domain : (T : Ty) → Ty
domain Bool = Bool
domain (T ⇒ _) = T

codomain : (T : Ty) → Ty
codomain Bool = Bool
codomain (_ ⇒ T) = T

⇒-inj : ∀ {A B A' B' : Ty} → A ⇒ B ≡ A' ⇒ B' → (A ≡ A') × (B ≡ B')
⇒-inj = ×⟨ cong domain , cong codomain ⟩

encodeB : Ty → Type
encodeB Bool = Ty
encodeB (B ⇒ B') = ⊥

_≟T_ : (A B : Ty) → Dec (A ≡ B)
Bool ≟T Bool = yes (λ i → Bool)
Bool ≟T (B ⇒ B₁) = no λ p → subst encodeB p Bool
(A ⇒ A₁) ≟T Bool = no (λ p → subst encodeB (λ i → p (~ i)) Bool )
(A ⇒ B) ≟T (A' ⇒ B') with A ≟T A' | B ≟T B'
... | yes pA | yes pB = yes (λ i → pA i ⇒ pB i)
... | yes pA | no ¬pB = no λ p → ¬pB (cong codomain p)
... | no ¬pA | yes pB = no λ p → ¬pA (cong domain p)
... | no ¬pA | no ¬pB = no λ p → ¬pA (cong domain p)

infixr 40 _⇒_

data Ctx : Type where
  ε   : Ctx
  _,_ : Ctx → Ty → Ctx


variable
  Γ Δ Ψ Φ : Ctx
  A B C : Ty


data Term : Ctx → Ty → Type

data Subst : Ctx → Ctx → Type

variable
  γ γ' : Subst Γ Δ
  δ : Subst Δ Ψ
  ψ : Subst Ψ Φ

  a a' : Term Γ A

data Subst where
  SId   : Subst Γ Γ
  SComp : Subst Δ Ψ → Subst Γ Δ → Subst Γ Ψ

  lid   : SComp SId γ ≡ γ
  rid   : SComp γ SId ≡ γ
  assoc : SComp γ (SComp δ ψ) ≡ SComp (SComp γ δ) ψ


  ⟨⟩ : Subst Γ ε
  ⟨⟩! : ∀ (x : Subst Γ ε) → x ≡ ⟨⟩

  ⟨_,_⟩ : Subst Γ Δ → Term Δ A → Subst Γ (Δ , A)

  p : Subst (Γ , A) Γ
  p∘⟨-,-⟩ : ∀ {Γ Δ} {γ : Subst Γ Δ} {a : Term Δ A} → SComp p ⟨ γ , a ⟩ ≡ γ



  set : ∀ (p q : γ ≡ γ') → p ≡ q

data Term where
  q : Term (Γ , A) A

  _[_] : Term Γ A → Subst Δ Γ → Term Δ A

  [][] : (a [ γ ]) [ δ ] ≡ a [ SComp γ δ ]
  [Id] : a [ SId ] ≡ a

  q[⟨-,-⟩] : q [ ⟨ γ , a ⟩ ] ≡ a [ γ ]


  lam : Term (Γ , A) B → Term Γ (A ⇒ B)
  app : Term Γ (A ⇒ B) → Term Γ A → Term Γ B

  β   : (bod : Term (Γ , A) B) → (a : Term Γ A) → app (lam bod) a ≡ bod [ ⟨ SId , a ⟩ ]
  η   : (f : Term Γ (A ⇒ B)) → f ≡ lam (app (f [ p ]) q)

  true false : Term Γ Bool

  if_then_else : Term Γ Bool → Term Γ A → Term Γ A → Term Γ A

  ite-true  : if true then a else a' ≡ a
  ite-false : if false then a else a' ≡ a'

module examples where
  not : Term ε (Bool ⇒ Bool)
  not = lam (if q then false else true)

  nand : Term ε (Bool ⇒ Bool ⇒ Bool)
  nand = lam (if q then lam (if q then false else true) else (lam true))


-- Categorical defintions

open import Categories.Category

-- Contexts and substitutions form a category

Ctxs : Category ℓ-zero ℓ-zero
Ctxs = Cat Ctx Subst

instance
  CtxsCat : IsCategory Ctxs
  IsCategory.Id CtxsCat = SId
  IsCategory._∘_ CtxsCat = SComp

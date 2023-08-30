module Theories.STLC.Model where

open import Cat.Prelude
open Precategory
open import Cat.Morphism

open import Cat.Instances.Product
open import Cat.CartesianClosed.Instances.PSh 
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Base
open Functor
open import Cat.Functor.Naturality
import Cat.Functor.Hom
import Cat.Functor.Hom.Representable
open import Cat.Functor.Compose

open _=>_
open _≅_

record STLC {ℓ ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  field
    𝓒 : Precategory ℓ ℓ'

  open Precategory 𝓒 public renaming (Ob to Ctx ; Hom to Sub)
  open Cat.Functor.Hom 𝓒 public
  open Binary-products (PSh ℓ' 𝓒) (PSh-products {κ = ℓ'} {C = 𝓒})
  open Cat.Functor.Hom.Representable {C = 𝓒} public
  open Representation

  field
    𝓒-term :  Terminal 𝓒

    Ty : Type ℓ
    -- ty-set : is-set Ty

    𝕋 : Ty → Ob (PSh ℓ' 𝓒)

  Tm : Ty → Ctx → Type ℓ'
  Tm A Γ = ∣ 𝕋 A .F₀ Γ ∣

  _[_] : ∀ {A Γ Δ} → Tm A Δ → Sub Γ Δ → Tm A Γ
  _[_] {A} t γ = 𝕋 A .F₁ γ t

  field
    extend : Ty → Functor 𝓒 𝓒

  _⊕_ : Ctx → Ty → Ctx
  Γ ⊕ A = extend A .F₀ Γ

  field  
    extension : (Γ : Ctx) (A : Ty) → (Hom[-, Γ ] ⊗₀ 𝕋 A) ≅ⁿ Hom[-, Γ ⊕  A ]

  Tm[-⊕_,_] : Ty → Ty → PSh ℓ' 𝓒 .Ob
  Tm[-⊕ A , B ] = F∘-functor .F₀ ((𝕋 B) , Functor.op (extend A)) 


record STLC-Functor {ℓ ℓ'} (𝓜 𝓝 : STLC {ℓ} {ℓ'}) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC hiding (𝓒)
  open STLC 𝓜 using (𝓒)
  open STLC 𝓝 using () renaming (𝓒 to 𝓓) 

  field
    F : Functor 𝓒 𝓓

  field
    pres-⊤ : ∀ {T} → is-terminal 𝓒 T → is-terminal 𝓓 (F .F₀ T)
  
  field
    Fty : 𝓜 .Ty → 𝓝 .Ty

  field
    extend-natural : ∀ {A : 𝓜 .Ty} → F F∘ (𝓜 .extend A) ≡ 𝓝 .extend (Fty A) F∘ F

record STLC-lamβη {ℓ ℓ'}  (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc ℓ ⊔ ℓ') where
  open STLC stlc

  open Representation

  field
    _⇒_ : Ty → Ty → Ty
    lamβη : ∀ {A B : Ty} → Tm[-⊕ A , B ] ≅ⁿ 𝕋 (A ⇒ B)

  lam : ∀ {Γ} {A B} → Tm B (Γ ⊕ A) → Tm (A ⇒ B) Γ
  lam {Γ} = lamβη .to .η Γ 

  app : ∀ {Γ} {A B} → Tm (A ⇒ B) Γ → Tm B (Γ ⊕ A)
  app {Γ} = lamβη .from .η Γ 

record STLC-Bool {ℓ} {ℓ'} (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc ℓ ⊔ ℓ') where
  open STLC stlc

  -- TODO: rewrite in representable functor / natural isomorphism style as above

  field
    𝔹 : Ty
    
    tru fls : ∀ {Γ} → Tm 𝔹 Γ
    elim : ∀ {A} {Γ} → Tm 𝔹 Γ → (a b : Tm A Γ) → Tm A Γ

    elim-tru : ∀ {Γ} {A} {a b : Tm A Γ} → elim tru a b ≡ a
    elim-fls : ∀ {Γ} {A} {a b : Tm A Γ} → elim fls a b ≡ b

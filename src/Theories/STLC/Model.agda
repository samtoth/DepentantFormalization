{-# OPTIONS --allow-unsolved-metas #-}
module Theories.STLC.Model where

--open import 1Lab.Prelude
open import Cat.Prelude
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
open import Cat.Strict
open import Cat.Instances.Slice
open import Cat.Bi.Base
open import Cat.Displayed.Base

open import Theories.STLC.NatHelp

open _=>_
open _≅_

record STLC {ℓ ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  field
    𝓒 : Precategory ℓ ℓ'

  -- field
  --   𝓒-strict : is-strict 𝓒

  open Precategory 𝓒 public renaming (Ob to Ctx ; Hom to Sub ; _∘_ to _∘ᶜ_ ; id to Cid) using ()
  open Cat.Functor.Hom 𝓒
  open Binary-products (PSh ℓ' 𝓒) (PSh-products {κ = ℓ'} {C = 𝓒}) renaming (⟨_,_⟩ to ×⟨_,_⟩)
  open Cat.Functor.Hom.Representable {C = 𝓒} public
  open Representation

  field
    𝓒-term :  Terminal 𝓒

  ε : Ctx
  ε = 𝓒-term .Terminal.top

  ⟨⟩ : ∀ Γ → Sub Γ ε
  ⟨⟩ Γ = 𝓒-term .Terminal.has⊤ Γ .is-contr.centre

  ⟨⟩! : ∀ {Γ} (γ : Sub Γ ε) → ⟨⟩ Γ ≡ γ
  ⟨⟩! {Γ} γ i = 𝓒-term .Terminal.has⊤ Γ .paths γ i  

  field  
    Ty : Type ℓ
    -- ty-set : is-set Ty

  -- Tyₛ : Set ℓ
  -- Tyₛ = el Ty ty-set

  field
    𝕋 : Ty → Ob (PSh ℓ' 𝓒)

  Tm : Ty → Ctx → Type ℓ'
  Tm A Γ = ∣ 𝕋 A .F₀ Γ ∣

  _[_] : ∀ {A Γ Δ} → Tm A Δ → Sub Γ Δ → Tm A Γ
  _[_] {A} t γ = 𝕋 A .F₁ γ t

  _[Id] : ∀ {A Γ} → (t : Tm A Γ) → t [ Cid ] ≡ t
  t [Id] = λ i → 𝕋 _ .F-id i t

  field
    extend : Ty → Functor 𝓒 𝓒

  _⊕_ : Ctx → Ty → Ctx
  Γ ⊕ A = extend A .F₀ Γ

  field  
    extension : (Γ : Ctx) (A : Ty) → (Hom[-, Γ ] ⊗₀ 𝕋 A) ≅ⁿ Hom[-, Γ ⊕  A ]

  ⟨_,_⟩ : ∀ {Γ Δ A} → Sub Γ Δ → Tm A Γ → Sub Γ (Δ ⊕ A)
  ⟨_,_⟩ {Γ} {Δ} {A} γ a = extension Δ A .to .η Γ (γ , a)

  p : ∀ {Γ Δ A} → Sub Γ (Δ ⊕ A) → Sub Γ Δ
  p {Γ} {Δ} {A} γ = extension Δ A .from .η Γ γ .fst

  q : ∀ {Γ Δ A} → Sub Γ (Δ ⊕ A) → Tm A Γ
  q {Γ} {Δ} {A} γ = extension Δ A .from .η Γ γ .snd

  p⟨_,_⟩ : ∀ {Γ Δ A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → p ⟨ γ , t ⟩ ≡ γ
  p⟨_,_⟩ {Γ} {Δ} {A} γ t i = extension Δ A .invr i .η Γ (γ , t) .fst

  pqη : ∀ {Γ Δ A} → (γ : Sub Γ (Δ ⊕ A)) → ⟨ p γ , q γ ⟩ ≡ γ
  pqη {Γ} {Δ} {A} γ i = extension Δ A .invl i .η Γ γ

  ⟨_,_⟩∘_ : ∀ {Γ} {Δ} {Ψ} {A} → (γ : Sub Γ Δ) → (t : Tm A Γ) → (δ : Sub Ψ Γ ) → ⟨ γ , t ⟩ ∘ᶜ δ ≡ ⟨ γ ∘ᶜ δ , t [ δ ] ⟩
  ⟨_,_⟩∘_ {Γ} {Δ} {Ψ} {A} γ t δ i = extension Δ A .to .is-natural Γ Ψ δ (~ i) (γ , t) 

  Tm[-⊕_,_] : Ty → Ty → PSh ℓ' 𝓒 .Ob
  Tm[-⊕ A , B ] = (𝕋 B) F∘ Functor.op (extend A)


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
    F𝕋 : ∀ {A} → 𝓜 .𝕋 A => 𝓝 .𝕋 (Fty A) F∘ Functor.op F

    F-extend : ∀ {A B : 𝓜 .Ty}
               → 𝓜 .𝕋 B F∘ Functor.op (𝓜 .extend A) 
               => (𝓝 .𝕋 (Fty B) F∘ Functor.op (𝓝 .extend (Fty A))) F∘ Functor.op F
module SF  = STLC-Functor

STLCFid : ∀ {ℓ} {ℓ'} (a : STLC {ℓ} {ℓ'}) → STLC-Functor a a 
STLCFid m .STLC-Functor.F = Id
STLCFid m .STLC-Functor.pres-⊤ = λ x → x
STLCFid m .STLC-Functor.Fty = λ x → x
STLCFid {ℓ} {ℓ'} m .STLC-Functor.F𝕋 .η Γ x = x
STLCFid {ℓ} {ℓ'} m .STLC-Functor.F𝕋 .is-natural Γ Δ γ = funext λ _ → refl 
STLCFid m .STLC-Functor.F-extend = {!   !}
  
STLCF∘ : ∀ {ℓ ℓ'} {x y z : STLC {ℓ} {ℓ'}} → STLC-Functor y z → STLC-Functor x y → STLC-Functor x z
STLCF∘ f g .STLC-Functor.F = f .SF.F F∘ g .SF.F
STLCF∘ f g .STLC-Functor.pres-⊤ xt Γ = f .SF.pres-⊤ (g .SF.pres-⊤ xt) Γ
STLCF∘ f g .STLC-Functor.Fty x = f .SF.Fty (g .SF.Fty x)
STLCF∘ {ℓ} {ℓ'} {x} {y} {z} f g .STLC-Functor.F𝕋 = tran
  where open import Cat.Instances.Functor.Duality
  
        tran : x .STLC.𝕋 _ => z .STLC.𝕋 _ F∘ (Functor.op (f .SF.F F∘ g .SF.F))
        tran = (z .STLC.𝕋 _ ◀ opnt {F = f .SF.F} {G = g .SF.F}) ∘nt α→ ∘nt (f .SF.F𝕋 ▶ Functor.op (g .SF.F)) ∘nt (g .SF.F𝕋)
STLCF∘ f g .STLC-Functor.F-extend = {!   !} 

STLCs : ∀ {ℓ ℓ'} → Precategory (lsuc (ℓ ⊔ ℓ')) (lsuc (ℓ ⊔ ℓ'))
STLCs {ℓ} {ℓ'} .Ob = STLC {ℓ} {ℓ'}
STLCs .Hom = STLC-Functor  
STLCs .Hom-set x y = {!   !}
STLCs .id = STLCFid _
STLCs ._∘_ = STLCF∘
STLCs .idr f = {!   !}
STLCs .idl g = {!   !}
STLCs .assoc = {!   !}


record STLC-lamβη {ℓ ℓ'}  (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC stlc

  open Representation

  field
    _⇒_ : Ty → Ty → Ty
    lamβη : ∀ {A B : Ty} → Tm[-⊕ A , B ] ≅ⁿ 𝕋 (A ⇒ B)

  lam : ∀ {Γ} {A B} → Tm B (Γ ⊕ A) → Tm (A ⇒ B) Γ
  lam {Γ} = lamβη .to .η Γ 

  app : ∀ {Γ} {A B} → Tm (A ⇒ B) Γ → Tm B (Γ ⊕ A)
  app {Γ} = lamβη .from .η Γ 

record STLC-lam-F {ℓ ℓ'} {S T : STLC {ℓ} {ℓ'}} (𝓕 : STLC-Functor S T) (𝓜 : STLC-lamβη S) (𝓝 : STLC-lamβη T) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC-Functor 𝓕
  module S = STLC S
  module T = STLC T
  module 𝓜λ = STLC-lamβη 𝓜
  module 𝓝λ = STLC-lamβη 𝓝


  field
    pres-=> : ∀ A B → Fty A 𝓝λ.⇒ Fty B ≡ Fty (A 𝓜λ.⇒ B)
    pres-lamβη : ∀  {A B} → PathP (λ i → S.Tm[-⊕ A , B ] => T.𝕋 (pres-=> A B i) F∘ Functor.op F)
                               ((𝓝λ.lamβη .to ▶ Functor.op F) ∘nt F-extend)
                                (F𝕋 {A 𝓜λ.⇒ B} ∘nt 𝓜λ.lamβη .to)  

STLC-lams : ∀ {ℓ ℓ'} → Displayed (STLCs {ℓ} {ℓ'}) _ _ 
Displayed.Ob[ STLC-lams ] = STLC-lamβη
Displayed.Hom[ STLC-lams ] = STLC-lam-F
Displayed.Hom[ STLC-lams ]-set = {!   !}
STLC-lams .Displayed.id′ = {!   !}
STLC-lams .Displayed._∘′_ = {!   !}
STLC-lams .Displayed.idr′ = {!   !}
STLC-lams .Displayed.idl′ = {!   !}
STLC-lams .Displayed.assoc′ = {!   !}


record STLC-Bool {ℓ} {ℓ'} (stlc : STLC {ℓ} {ℓ'}) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC stlc

  -- TODO: rewrite in representable functor / natural isomorphism style as above

  field
    𝔹 : Ty
    
    tru fls : ∀ {Γ} → Tm 𝔹 Γ
    elim : ∀ {A} {Γ} → Tm 𝔹 Γ → (a b : Tm A Γ) → Tm A Γ

    elim-tru : ∀ {Γ} {A} {a b : Tm A Γ} → elim tru a b ≡ a
    elim-fls : ∀ {Γ} {A} {a b : Tm A Γ} → elim fls a b ≡ b


record STLC-Bool-F {ℓ ℓ'} {S T : STLC {ℓ} {ℓ'}} (𝓕 : STLC-Functor S T) (𝓜 : STLC-Bool S) (𝓝 : STLC-Bool T) : Type (lsuc (ℓ ⊔ ℓ')) where
  open STLC-Functor 𝓕
  open STLC-Bool
  
  field
    pres-𝔹 : Fty (𝓜 .𝔹) ≡ 𝓝 .𝔹 

    pres-tru : ∀ {Γ} → PathP (λ i → ∣ T .STLC.𝕋 (pres-𝔹 i) .F₀ (F .F₀ Γ) ∣) (F𝕋 .η Γ (𝓜 .tru)) (𝓝 .tru)
    pres-fls : ∀ {Γ} → PathP (λ i → ∣ T .STLC.𝕋 (pres-𝔹 i) .F₀ (F .F₀ Γ) ∣) (F𝕋 .η Γ (𝓜 .fls)) (𝓝 .fls)
     

STLC-Bools : ∀ {o ℓ} → Displayed (STLCs {o} {ℓ}) _ _
Displayed.Ob[ STLC-Bools {o} {ℓ} ] = STLC-Bool
Displayed.Hom[ STLC-Bools {o} {ℓ} ] = STLC-Bool-F
Displayed.Hom[ STLC-Bools {o} {ℓ} ]-set = {!   !}
STLC-Bools {o} {ℓ} .Displayed.id′ = {!   !}
STLC-Bools {o} {ℓ} .Displayed._∘′_ = {!   !}
STLC-Bools {o} {ℓ} .Displayed.idr′ = {!   !}
STLC-Bools {o} {ℓ} .Displayed.idl′ = {!   !}
STLC-Bools {o} {ℓ} .Displayed.assoc′ = {!   !}

_⊗_ : ∀ {l m k n} {C : Precategory l m} → (A  B : Displayed C k n) → Displayed C k n
A ⊗ B = the-display
  where module A = Displayed A
        module B = Displayed B
        the-display : Displayed _ _ _
        Displayed.Ob[ the-display ] = λ x → A.Ob[ x ] × B.Ob[ x ]
        Displayed.Hom[ the-display ] = λ cf x y → A.Hom[ cf ] (x .fst) (y .fst) × B.Hom[ cf ] (x .snd) (y .snd)
        Displayed.Hom[ the-display ]-set = λ _ _ _ → hlevel!
        the-display .Displayed.id′ = A.id′ , B.id′
        the-display .Displayed._∘′_ = λ f g → (f .fst A.∘′ g .fst , f .snd B.∘′ g .snd)
        the-display .Displayed.idr′ = {!   !}
        the-display .Displayed.idl′ = {!   !}
        the-display .Displayed.assoc′ = {!   !}


STLC-lam-bool : ∀ {o} {ℓ} → Displayed (STLCs {o} {ℓ}) _ _
STLC-lam-bool = STLC-lams ⊗ STLC-Bools

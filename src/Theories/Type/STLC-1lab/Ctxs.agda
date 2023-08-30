module Theories.STLC.Ctxs  where

open import 1Lab.Prelude
open import Cat.Prelude
open import Data.Dec
open import Cat.Functor.Base
open import Cat.Diagram.Terminal
import Cat.Reasoning
open Functor

data Ty : Type where
  𝔹 : Ty
  _⇒_  : Ty → Ty → Ty
 

domain : Ty → Ty → Ty
domain a 𝔹 = a
domain _ (T ⇒ _) = T

codomain : Ty → Ty → Ty
codomain a 𝔹 = a
codomain _ (_ ⇒ T) = T

⇒-inj : ∀ {A B A' B' : Ty} → A ⇒ B ≡ A' ⇒ B' → (A ≡ A') × (B ≡ B')
⇒-inj x = (λ i → domain 𝔹 (x i)) , (λ i → codomain 𝔹 (x i))


CodeT : Ty → Ty → Type
CodeT 𝔹 𝔹 = ⊤
CodeT 𝔹 (_ ⇒ _) = ⊥
CodeT (A ⇒ B) (A' ⇒ B') = CodeT A A' × CodeT B B'
CodeT (_ ⇒ _) 𝔹 = ⊥ 

_≟T_ : (A B : Ty) → Dec (A ≡ B)
𝔹 ≟T 𝔹 = yes refl
𝔹 ≟T (y ⇒ y₁) = no (λ P → subst (CodeT 𝔹) P tt)
(x ⇒ y) ≟T 𝔹 = no (λ P → subst (CodeT 𝔹) (sym P) tt)
(x ⇒ y) ≟T (x' ⇒ y') with x ≟T x' | y ≟T y' 
... | yes pX | yes pY = yes (λ i → (pX i) ⇒ (pY i))
... | yes pX | no ¬pY = no (λ P → ¬pY (λ i → codomain (pX i) (P i)))
... | no ¬pX | yes pY = no (λ P → ¬pX (λ i → domain (pY i) (P i)))
... | no ¬pX | no ¬pY = no (λ P → ¬pX (λ i → domain (P i) (P i)))

Ty-is-set : is-set Ty
Ty-is-set = Discrete→is-set _≟T_

infixr 40 _⇒_

data Ctx : Type where
  ε   : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ Δ Ψ Φ : Ctx
  A B C : Ty

,-inj : Path Ctx (Γ , A) (Δ , B) → (Γ ≡ Δ) × (A ≡ B)
,-inj {A = A} {B = B} x = ap (fst ∘ un, (ε , A)) x , ap (snd ∘ un, (ε , B)) x
  where un, : Ctx × Ty → Ctx → Ctx × Ty
        un, a ε = a
        un, a (x , x') = x , x'


CodeCtx : Ctx → Ctx → Type
CodeCtx ε ε = ⊤
CodeCtx ε (Δ , x) = ⊥
CodeCtx (Γ , x) ε = ⊥
CodeCtx (Γ , x) (Δ , y) = CodeCtx Γ Δ × (x ≡ y)

Ctx-discrete : Discrete Ctx
Ctx-discrete ε ε = yes refl
Ctx-discrete ε (y , x) = no λ P → subst (CodeCtx ε) P tt
Ctx-discrete (xs , x) ε = no λ P → subst (CodeCtx ε) (sym P) tt
Ctx-discrete (xs , x) (ys , y) with Ctx-discrete xs ys | x ≟T y
... | yes xsP | yes xP = yes (λ i → xsP i ,  xP i)
... | yes _ | no ¬a = no (λ P → ¬a (,-inj P .snd))
... | no ¬a | yes _ = no λ P → ¬a (,-inj P .fst)
... | no ¬a | no ¬_ = no λ P → ¬a (,-inj P .fst)

Ctx-is-set : is-set Ctx
Ctx-is-set = Discrete→is-set Ctx-discrete

module CtxSubs where

  data Subst (T : Ctx → Ty → Type) : Ctx → Ctx → Type 

  private variable
    T : Ctx → Ty → Type
  variable
    γ γ' : Subst T Γ Δ
    δ : Subst T Δ Ψ
    ψ : Subst T Ψ Φ


  data Subst T where
    SId   : Subst T Γ Γ
    SComp : Subst T Δ Ψ → Subst T Γ Δ → Subst T Γ Ψ

    lid   : SComp SId γ ≡ γ
    rid   : SComp γ SId ≡ γ
    Sassoc : SComp γ (SComp δ ψ) ≡ SComp (SComp γ δ) ψ


    ⟨⟩ : Subst T Γ ε
    ⟨⟩! : ∀ (x : Subst T Γ ε) → x ≡ ⟨⟩

    ⟨_,_⟩ : Subst T Γ Δ → T Γ A → Subst T Γ (Δ , A)
    
    p : Subst T (Γ , A) Γ
    p∘⟨_,_⟩ : ∀ {Γ Δ} (γ : Subst T Γ Δ) (a : T Γ A) → SComp p ⟨ γ , a ⟩ ≡ γ

    trunc : ∀ (Γ Δ : Ctx) → is-set (Subst T Γ Δ)




-- Categorical defintions

module Ctxs-cat (T : Ctx → Ty → Type)
                      where
 

  open CtxSubs

  -- Contexts and substitutions form a category

  Ctxs : Precategory lzero lzero
  Ctxs .Precategory.Ob = Ctx
  Ctxs .Precategory.Hom = Subst T
  Ctxs .Precategory.Hom-set = trunc
  Ctxs .Precategory.id = SId
  Ctxs .Precategory._∘_ = SComp
  Ctxs .Precategory.idr _ = rid
  Ctxs .Precategory.idl _ = lid
  Ctxs .Precategory.assoc _ _ _ = Sassoc

  open Precategory Ctxs renaming (_∘_ to _∘s_ )
  open Cat.Reasoning Ctxs hiding (_∘_)


  Ctxs-terminal : Terminal Ctxs
  Ctxs-terminal .Terminal.top = ε
  Ctxs-terminal .Terminal.has⊤ = λ x → contr ⟨⟩ (sym ∘ ⟨⟩!)


  module CtxExtension (q : ∀ {Γ'} {A'} → T (Γ' , A') A')
      (_[_] : ∀ {Γ' Δ'} {A'} → T Γ' A' → Subst T Δ' Γ' → T Δ' A')
      (_[Id] : ∀ {Γ'} {A'} → (t : T Γ' A') → t [ SId ] ≡ t)
      (_[_][_] : ∀ {Γ' Δ' Ψ'} {A'} (a : T Ψ' A') (γ : Subst T Δ' Ψ') (δ : Subst T Γ' Δ') → (a [ γ ]) [ δ ] ≡ a [ γ ∘s δ ])
      (q[⟨_,_⟩] : ∀ {Γ' Δ'} {A'} (γ : Subst T Γ' Δ') (a : T Γ' A') → q [ ⟨ γ , a ⟩ ] ≡ a)
      ([⟨_,_⟩][_] : ∀ {Γ' Δ' Ψ'} {A'} {t} (γ : Subst T Γ' Δ') (a : T Γ' A') (δ : Subst T Ψ' Γ') → Path (T Ψ' A') ((t [ ⟨ γ , a ⟩ ]) [ δ ]) (t [ ⟨ γ ∘s δ , a [ δ ] ⟩ ]))
          where


    postulate
        ⟨_,_⟩∘_ : ∀ (γ : Subst T Γ Δ) (a : T Γ A) (δ : Subst T Ψ Γ) 
                  → ⟨ γ , a ⟩ ∘s δ ≡ ⟨ γ ∘s δ , a [ δ ] ⟩

    ⟨p,q⟩ : Path (Subst T (Γ , A) (Γ , A)) ⟨ p , q ⟩ SId 
    ⟨p,q⟩ = trust
      where postulate trust : ∀ {A} → A

    
    wk : Subst T Γ Δ → (A : Ty) → Subst T (Γ , A) (Δ , A)
    wk γ _ = ⟨ γ ∘s p , q ⟩

    wk∘ : wk γ A ∘s wk δ A ≡ wk (γ ∘s δ) A
    wk∘ {γ = γ} {δ = δ} = ⟨ γ ∘s p , q ⟩ ∘s ⟨ δ ∘s p , q ⟩
                ≡⟨ (⟨ _ , _ ⟩∘ _) ⟩
             ⟨ (γ ∘s p) ∘s ⟨ δ ∘s p , q ⟩ , q [ ⟨ δ ∘s p , q ⟩ ] ⟩
                ≡⟨ (λ i → ⟨ (sym (Sassoc {γ = γ}) ∙ (refl ⟩∘⟨ p∘⟨ δ ∘s p , q ⟩) ) i , q[⟨ δ ∘s p , q ⟩] i ⟩) ⟩
             ⟨ γ ∘s ( δ ∘s p) , q ⟩
                ≡⟨ (λ i → ⟨ Sassoc {γ = γ} {δ = δ} {ψ = p} i , q ⟩) ⟩
              ⟨ (γ ∘s δ) ∘s p , q ⟩ ∎

    generic-ctx-extension : ∀ Ty → Functor Ctxs Ctxs
    generic-ctx-extension A .F₀ = _, A
    generic-ctx-extension A .F₁ γ = ⟨ SComp γ p , q ⟩
    generic-ctx-extension A .F-id {Γ} = ap ⟨_, q ⟩ lid ∙ ⟨p,q⟩
    generic-ctx-extension A .F-∘ f g = sym wk∘
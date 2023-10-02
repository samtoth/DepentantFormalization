{-# OPTIONS --allow-unsolved-metas #-}
module Theories.STLC.Contextual where

open import 1Lab.Prelude
open import Theories.STLC.Ctxs
open import Theories.STLC.Model

record Contextual {ℓ ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
    field Typ : Type ℓ
    field TrmSet : Ctx (Typ) → Typ → Set (ℓ ⊔ ℓ')
    Trm = λ Γ A → ∣ TrmSet Γ A ∣ 
    CSub = Subst Trm
    field _[_]C : ∀ {Γ A} → Trm Γ A → CSub Δ Γ → Trm Δ A
    field Cid   : ∀ {Γ} → CSub Γ Γ
    
    infixl 20 _⊚_
    _⊚_ : {Γ Δ Σ : Ctx Typ} → CSub Δ Σ → CSub Γ Δ → CSub Γ Σ
    γ ⊚ δ = mapEls _[ δ ]C γ

    field idL : {Γ Δ : Ctx Typ} (σ : CSub Γ Δ) → Cid ⊚ σ ≡ σ
    field _[id]C : {Γ : Ctx Typ} {A : Typ} (t : Trm Γ A) → t [ Cid ]C ≡ t
 
    ε! : ∀ (γ : CSub Γ ε) → ! ≡ γ
    ε! ! = refl

    cvz : ∀ {Γ A} → Trm (Γ , A) A
    cvz = qEls Cid

    cvsuc : ∀ {Γ A} → CSub (Γ , A) Γ
    cvsuc = pEls Cid

    wk1 : ∀ {A} → CSub Γ Δ → CSub (Γ , A) Δ
    wk1 ! = !
    wk1 (γ ⊕ x) = wk1 γ ⊕ (x [ cvsuc ]C)

    wk2 : ∀ {A} → CSub Γ Δ → CSub (Γ , A) (Δ , A)
    wk2 γ = wk1 γ ⊕ cvz

    wk2id : ∀ {A} → wk2 {Γ} {Γ} {A} Cid ≡ Cid
    wk2id = {!   !}

module _ {ℓ} {ℓ'} (cx : Contextual {ℓ} {ℓ'}) where
    open import Cat.Base
    open import Cat.Functor.Naturality
    open Contextual cx
    private
     cat : Precategory _ _
     cat .Precategory.Ob = Ctx Typ
     cat .Precategory.Hom = CSub
     cat .Precategory.Hom-set = {!   !}
     cat .Precategory.id = Cid
     cat .Precategory._∘_ = _⊚_
     cat .Precategory.idr = {!   !}
     cat .Precategory.idl = idL
     cat .Precategory.assoc = {!   !}

     𝕋 : ∀ (A : Typ) → Functor (cat ^op) (Sets (ℓ ⊔ ℓ'))
     𝕋 A .Functor.F₀ Γ = TrmSet Γ A 
     𝕋 A .Functor.F₁ = λ γ x → x [ γ ]C
     𝕋 A .Functor.F-id = {!  !}
     𝕋 A .Functor.F-∘ = {!   !}

     extendF : Typ → Functor cat cat
     extendF A .Functor.F₀ = _, A
     extendF A .Functor.F₁ = wk2
     extendF A .Functor.F-id = {!   !}
     extendF A .Functor.F-∘ = {!   !}

    ContextualModel : STLC 
    ContextualModel .STLC.𝓒 = cat
    ContextualModel .STLC.𝓒-strict = {!   !}
    ContextualModel .STLC.𝓒-term = record { top = ε ; has⊤ = λ _ → contr ! ε! }
    ContextualModel .STLC.Ty = Typ
    ContextualModel .STLC.𝕋 = 𝕋
    ContextualModel .STLC.extend = extendF
    ContextualModel .STLC.extension Γ A = to-natural-iso the-iso
        where the-iso : make-natural-iso _ _
              the-iso .make-natural-iso.eta _ (γ , x) = γ ⊕ x
              the-iso .make-natural-iso.inv _  (γ ⊕ x) = γ , x
              the-iso .make-natural-iso.eta∘inv _ i (γ ⊕ x) = (γ ⊕ x)
              the-iso .make-natural-iso.inv∘eta _ i (γ , x) = γ , x
              the-iso .make-natural-iso.natural _ _ γ i (δ , t) = mapEls (λ e → e [ γ ]C) δ ⊕ (t [ γ ]C)  
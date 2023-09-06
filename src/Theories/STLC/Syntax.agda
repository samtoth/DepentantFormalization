{-# OPTIONS --two-level --allow-unsolved-metas #-}
module Theories.STLC.Syntax where

open import 1Lab.Prelude
open import Cat.Prelude
open import Cat.Diagram.Product

open import Data.Dec

open import Theories.STLC.Ctxs


data Term : Ctx → Ty → Type 

TSubst = Subst Term

variable
  a a' : Term Γ A


data Term  where
  q : Term (Γ , A) A

  _[_] : Term Γ A → TSubst Δ Γ → Term Δ A

  _[_][_] : ∀ {Γ Δ Ψ} {A}
            → (a : Term Ψ A) (δ : TSubst Δ Ψ) (γ : TSubst Γ Δ) 
            → (a [ δ ]) [ γ ] ≡ a [  SComp δ γ ]
  _[Id] : ∀ (a : Term Γ A) → a [ SId ] ≡ a

  q[⟨_,_⟩] : ∀ {Γ Δ} (γ : TSubst Γ Δ) (a : Term Γ A) → q [ ⟨ γ , a ⟩ ] ≡ a

  lam : Term (Γ , A) B → Term Γ (A ⇒ B)
  lam[] : ∀ {A B : Ty} (b : Term (Γ , A) B) → (lam b) [ γ ] ≡ lam (b [ ⟨ SComp γ p , q ⟩ ]) 
  app : Term Γ (A ⇒ B) → Term Γ A → Term Γ B

  β   : (bod : Term (Γ , A) B) → (a : Term Γ A) → app (lam bod) a ≡ bod [ ⟨ SId , a ⟩ ]
  η   : (f : Term Γ (A ⇒ B)) → f ≡ lam (app (f [ p ]) q)

  true false : Term Γ 𝔹

  if_then_else : Term Γ 𝔹 → Term Γ A → Term Γ A → Term Γ A

  ite-true  : if true then a else a' ≡ a
  ite-false : if false then a else a' ≡ a'

  trunc : ∀ {Γ} {A} → is-set (Term Γ A)

module examples where
  not : Term ε (𝔹 ⇒ 𝔹)
  not = lam (if q then false else true)

  nand : Term ε (𝔹 ⇒ 𝔹 ⇒ 𝔹)
  nand = lam (if q then lam (if q then false else true) else (lam true))



module is-model where
  open import Theories.STLC.Model
  open import Theories.STLC.Ctxs
  open Ctxs-cat (Term)


  open import Cat.Morphism using (_≅_)
  open import Cat.Diagram.Product
  open import Cat.Functor.Naturality
  open import Cat.Functor.Base
  open import Cat.Functor.Hom Ctxs
  open import Cat.CartesianClosed.Instances.PSh 
  import Cat.Reasoning
  open Functor
  open Binary-products (PSh lzero Ctxs) (PSh-products {κ = lzero} {C = Ctxs}) hiding (⟨_,_⟩)

  open Precategory Ctxs renaming (_∘_ to _∘s_ ; assoc to assocₛ)
  open Cat.Reasoning Ctxs hiding (_∘_)




  pq-inj : ∀ {γ δ : Subst Term Γ (Δ , A)} → p ∘s γ ≡ p ∘s δ → q [ γ ] ≡ q [ δ ] → γ ≡ δ
  pq-inj {ε} {ε} {γ = γ} {δ} = {! γ  !}
  pq-inj {ε} {Δ , x} = {!   !}
  pq-inj {Γ , x} {ε} = {!   !}
  pq-inj {Γ , x} {Δ , x₁} = {!   !}
  
  open CtxExtension q _[_] _[Id] _[_][_] q[⟨_,_⟩] pq-inj

  private
    𝕋 : Ty → Precategory.Ob (PSh lzero Ctxs)
    𝕋 A .F₀ Γ = el (Term Γ A) trunc
    𝕋 A .F₁ γ t = t [ γ ]
    𝕋 A .F-id i t = (t [Id]) i
    𝕋 A .F-∘ f g i t = (t [ g ][ f ]) (~ i)


  syn : STLC {lzero} {lzero}
  syn .STLC.𝓒 = Ctxs
  syn .STLC.𝓒-term = Ctxs-terminal
  syn .STLC.Ty = Ty
  -- syn .STLC.ty-set = Ty-is-set
  syn .STLC.𝕋 = 𝕋
  syn .STLC.extend = generic-ctx-extension
  syn .STLC.extension Γ A = to-natural-iso the-iso
    where the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ 𝕋 A) Hom[-, Γ , A ]
          the-iso .make-natural-iso.eta Γ (γ , a) = ⟨ γ , a ⟩
          the-iso .make-natural-iso.inv Γ γ = (p ∘s γ) , (q [ γ ])
          the-iso .make-natural-iso.eta∘inv Γ = funext (λ γ → pq-inj p∘⟨ _ , _ ⟩ q[⟨ _ , _ ⟩])
          the-iso .make-natural-iso.inv∘eta Γ = funext (λ γ i → (p∘⟨ γ .fst , γ .snd ⟩ i) , q[⟨ γ .fst , γ .snd ⟩] i)
          the-iso .make-natural-iso.natural Γ Δ γ = funext (λ x → pq-inj
                          ( p ∘s (⟨ x .fst , x .snd ⟩ ∘s γ)
                                 ≡⟨ assoc p _ γ ⟩
                            (p ∘s ⟨ x .fst , x .snd ⟩) ∘s γ
                                 ≡⟨ p∘⟨ _ , _ ⟩  ⟩∘⟨ refl ⟩
                            x .fst ∘s γ
                                 ≡⟨ sym p∘⟨ _ , _ ⟩ ⟩
                            p ∘s ⟨ x .fst ∘s γ , x .snd [ γ ] ⟩ ∎
                          )
                          ( q [ ⟨ x .fst , x .snd ⟩ ∘s γ  ]
                              ≡⟨ sym (q [ _ ][ γ ]) ⟩
                            (q [ ⟨ x .fst , x .snd ⟩ ]) [ γ ]
                              ≡⟨ ap (_[ γ ]) q[⟨ _ , _ ⟩] ⟩
                            x .snd [ γ ]
                              ≡⟨ sym q[⟨ _ , _ ⟩] ⟩
                            q [ ⟨ x .fst ∘s γ , x .snd [ γ ] ⟩ ] ∎
                          ))
          
          
  syn-λβη : STLC-lamβη syn
  syn-λβη .STLC-lamβη._⇒_ = _⇒_
  syn-λβη .STLC-lamβη.lamβη = to-natural-iso the-iso
    where open STLC syn using (Tm[-⊕_,_] ; extension)
          the-iso : make-natural-iso Tm[-⊕ A , B ] (𝕋 (A ⇒ B))
          the-iso .make-natural-iso.eta Γ bod = lam bod
          the-iso .make-natural-iso.inv Γ f = app (f [ p ]) q
          the-iso .make-natural-iso.eta∘inv Γ = funext (sym ∘ η)
          the-iso .make-natural-iso.inv∘eta Γ = funext λ x → 
                  app (lam x [ p ]) q                
                    ≡⟨ ap (λ k → app k q) (lam[] x) ⟩
                  app (lam (x [ ⟨ p ∘s p , q ⟩ ])) q 
                    ≡⟨ β (x [ _ ]) q ⟩
                  (x [ ⟨ p ∘s p , q ⟩ ]) [ ⟨ SId , q ⟩ ]          
                    ≡⟨ (x [ _ ][ ⟨ SId , q ⟩ ]) ⟩
                  x [ ⟨ p ∘s p , q ⟩ ∘s ⟨ SId , q ⟩ ]
                    ≡⟨ ap (x [_]) {!   !} ⟩
                  x [ ⟨ (p ∘s p) ∘s ⟨ SId , q ⟩ , q [ ⟨ SId , q ⟩ ] ⟩ ] 
                    ≡⟨ {!   !} ⟩
                  x [ p ∘s ⟨ SId , q ⟩ ]             
                    ≡⟨ ap (x [_]) p∘⟨ _ , _ ⟩ ⟩
                  x [ SId ]                          ≡⟨ (x [Id]) ⟩
                  x                                  ∎
          the-iso .make-natural-iso.natural Γ Δ γ = funext lam[]


  syn-bool : STLC-Bool syn
  syn-bool .STLC-Bool.𝔹 = 𝔹
  syn-bool .STLC-Bool.tru = true
  syn-bool .STLC-Bool.fls = false
  syn-bool .STLC-Bool.elim = if_then_else
  syn-bool .STLC-Bool.elim-tru = ite-true
  syn-bool .STLC-Bool.elim-fls = ite-false 
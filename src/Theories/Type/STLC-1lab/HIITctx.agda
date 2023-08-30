module Theories.STLC.HIITctx where

open import 1Lab.Prelude

open import Theories.STLC.Ctxs

data 𝓘 : Type where Tm Sub : 𝓘

args : 𝓘 → Type
args Tm = Ctx × Ty
args Sub = Ctx × Ctx

data ιSTLC : (i : 𝓘) → args i → Type where
  Id   : ιSTLC Sub (Γ , Γ)
  Comp : ιSTLC Sub (Δ , Ψ) → ιSTLC Sub (Γ , Δ) → ιSTLC Sub (Γ , Ψ)

  lid    : ∀ (γ : ιSTLC Sub (Γ , Δ))  → Comp Id γ ≡ γ
  rid    : ∀ (γ : ιSTLC Sub (Γ , Δ)) → Comp γ Id ≡ γ
  Sassoc : ∀ (γ : ιSTLC Sub (Ψ , Φ)) (δ : ιSTLC Sub (Δ , Ψ)) (ψ : ιSTLC Sub (Γ , Δ))
             → Comp γ (Comp δ ψ) ≡ Comp (Comp γ δ) ψ

  ⟨⟩  : ιSTLC Sub (Γ , ε)
  ⟨⟩! : ∀ (γ : ιSTLC Sub (Γ , ε)) → ⟨⟩ ≡ γ

  ⟨_,_⟩ : ιSTLC Sub (Γ , Δ) → ιSTLC Tm (Γ , A) → ιSTLC Sub (Γ , (Δ , A))
  

  p : ιSTLC Sub (Γ , (Δ , A)) → ιSTLC Sub (Γ , Δ)
  q : ιSTLC Sub (Γ , (Δ , A)) → ιSTLC Tm  (Γ , A)

  p⟨_,_⟩ : ∀ (γ : ιSTLC Sub (Γ , Δ)) (a : ιSTLC Tm (Γ , A)) → p ⟨ γ , a ⟩ ≡ γ
  q⟨_,_⟩ : ∀ (γ : ιSTLC Sub (Γ , Δ)) (a : ιSTLC Tm (Γ , A)) → q ⟨ γ , a ⟩ ≡ a

  pqη : ∀ (γ : ιSTLC Sub (Γ , (Δ , A))) → ⟨ p γ , q γ ⟩ ≡ γ

  _[_] : ιSTLC Tm (Δ , A) → ιSTLC Sub (Γ , Δ) → ιSTLC Tm (Γ , A)

  pβ : ∀ {γ : ιSTLC Sub (Γ , Δ)} {a : ιSTLC Tm (Γ , A)} → p ⟨ γ , a ⟩ ≡ γ
  qβ : ∀ {γ : ιSTLC Sub (Γ , Δ)} {a : ιSTLC Tm (Γ , A)} → q ⟨ γ , a ⟩ ≡ a

  _[Id] : (t : ιSTLC Tm (Γ , A))  → t [ Id ] ≡ t

  _[_][_]  : ∀ (t : ιSTLC Tm (Ψ , A)) (γ : ιSTLC Sub (Δ , Ψ)) (δ : ιSTLC Sub (Γ , Δ)) 
             → (t [ γ ]) [ δ ] ≡ t [ Comp γ δ ]

  ⟨_,_⟩∘_ : ∀ (γ : ιSTLC Sub (Γ , Δ)) (a : ιSTLC Tm (Γ , A)) (δ : ιSTLC Sub (Ψ , Γ))
            → Comp ⟨ γ , a ⟩ δ ≡ ⟨ Comp γ δ , a [ δ ] ⟩ 

  ιSTLC-is-set : ∀ i a → is-set (ιSTLC i a)


open import Theories.STLC.Model
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude 
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.CartesianClosed.Instances.PSh 
open Precategory using (Ob)



Subs : Precategory lzero lzero
Subs .Precategory.Ob = Ctx
Subs .Precategory.Hom x y = ιSTLC Sub (x , y)
Subs .Precategory.Hom-set x y = ιSTLC-is-set Sub (x , y)
Subs .Precategory.id = ιSTLC.Id
Subs .Precategory._∘_ = Comp
Subs .Precategory.idr = rid
Subs .Precategory.idl = lid
Subs .Precategory.assoc = Sassoc

open Precategory Subs hiding (Ob) renaming (_∘_ to _∘s_; id to Sid)
open import Cat.Functor.Hom Subs
open Binary-products (PSh lzero Subs) (PSh-products {κ = lzero} {C = Subs}) hiding (⟨_,_⟩)


_↑_ : ιSTLC Sub (Γ , Δ) → (A : Ty) → ιSTLC Sub ((Γ , A) , (Δ , A))
γ ↑ A = ⟨ γ ∘s (p Sid) , q Sid ⟩

Id↑_  : ∀ {Γ} A → Sid {Γ} ↑ A ≡ Sid
Id↑_ {Γ} A = ⟨ Sid ∘s p Sid , q Sid ⟩ 
          ≡⟨ ap  ⟨_, q Sid ⟩ (lid (p Sid)) ⟩ 
        ⟨ p Sid , q Sid ⟩ 
          ≡⟨ pqη Sid ⟩ 
        Sid ∎


p∘⟨_,_⟩ : ∀ (γ : Hom Γ Δ) (a : ιSTLC Tm (Γ , A)) → p Sid ∘s ⟨ γ , a ⟩ ≡ γ
p∘⟨ γ , a ⟩ = {!   !}

∘↑  : (f : Hom Δ Ψ)
      (g : Hom Γ Δ) →
      (f ∘s g ↑ A) ≡ (f ↑ A) ∘s (g ↑ A)
∘↑ f g = sym (⟨ f ∘s p Sid , q Sid ⟩ ∘s ⟨ g ∘s p Sid , q Sid ⟩ 
                  ≡⟨ {!   !} ⟩
              ⟨ (f ∘s g) ∘s p Sid , q Sid ⟩ ∎)

SubsTerminal : Terminal Subs
SubsTerminal .Terminal.top = ε
SubsTerminal .Terminal.has⊤ = λ x → contr ⟨⟩ ⟨⟩!

ι𝕋 : Ty → PSh lzero Subs .Ob
ι𝕋 A .Functor.F₀ Γ = el (ιSTLC Tm (Γ , A)) (ιSTLC-is-set Tm (Γ , A))
ι𝕋 A .Functor.F₁ γ a = a [ γ ]
ι𝕋 A .Functor.F-id = funext (λ t → t [Id])
ι𝕋 A .Functor.F-∘ f g = funext (λ t → sym (t  [ g ][ f ]))

extend : Ty → Functor Subs Subs
extend A .Functor.F₀ = _, A
extend A .Functor.F₁ = _↑ A
extend A .Functor.F-id = Id↑ A
extend A .Functor.F-∘ = ∘↑

ιSTLC-model : STLC 
ιSTLC-model .STLC.𝓒 = Subs
ιSTLC-model .STLC.𝓒-term = SubsTerminal
ιSTLC-model .STLC.Ty = Ty
ιSTLC-model .STLC.𝕋 = ι𝕋
ιSTLC-model .STLC.extend = extend
ιSTLC-model .STLC.extension Γ A = to-natural-iso the-iso 
  where the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ (ι𝕋 A)) Hom[-, Γ , A ] 
        the-iso .make-natural-iso.eta Γ (γ , a) = ⟨ γ , a ⟩
        the-iso .make-natural-iso.inv Γ γ = p γ , q γ
        the-iso .make-natural-iso.eta∘inv Γ = funext pqη
        the-iso .make-natural-iso.inv∘eta Γ = funext λ x i → pβ {γ = x .fst} {a = x .snd} i , qβ {γ = x .fst} {a = x .snd} i
        the-iso .make-natural-iso.natural Γ Δ γ = funext (λ x → ⟨ x .fst , x .snd ⟩∘ γ) 


data ιSTLC-lam : (i : 𝓘) → args i → Type where
  stlc : ∀ {i a} → ιSTLC i a → ιSTLC-lam i a

  
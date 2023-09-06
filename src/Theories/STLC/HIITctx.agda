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


  _[Id] : (t : ιSTLC Tm (Γ , A))  → t [ Id ] ≡ t

  _[_][_]  : ∀ (t : ιSTLC Tm (Ψ , A)) (γ : ιSTLC Sub (Δ , Ψ)) (δ : ιSTLC Sub (Γ , Δ)) 
             → (t [ γ ]) [ δ ] ≡ t [ Comp γ δ ]

  ⟨_,_⟩∘_ : ∀ (γ : ιSTLC Sub (Γ , Δ)) (a : ιSTLC Tm (Γ , A)) (δ : ιSTLC Sub (Ψ , Γ))
            → Comp ⟨ γ , a ⟩ δ ≡ ⟨ Comp γ δ , a [ δ ] ⟩ 

  -- lam ≅ app  
  lam : ιSTLC Tm ((Γ , A) , B) → ιSTLC Tm (Γ , (A ⇒ B))
  app : ιSTLC Tm (Γ , (A ⇒ B)) → ιSTLC Tm ((Γ , A) , B)

  lamη : ∀ (f : ιSTLC Tm (Γ , (A ⇒ B))) → lam (app f) ≡ f  
  appβ : ∀ (f : ιSTLC Tm ((Γ , A) , B)) → app (lam f) ≡ f

  lam[] : ∀ (f : ιSTLC Tm ((Γ , A) , B)) (γ : ιSTLC Sub (Δ , Γ)) → lam f [ γ ] ≡ lam (f [ ⟨ Comp γ (p Id) , q Id ⟩ ]) 

  true false : ιSTLC Tm (Γ , 𝔹)
  elim𝔹 : ιSTLC Tm (Γ , 𝔹) → ιSTLC Tm (Γ , A) → ιSTLC Tm (Γ , A) → ιSTLC Tm (Γ , A)  
  elimT : ∀ (a b : ιSTLC Tm (Γ , A)) → elim𝔹 true a b ≡ a
  elimF : ∀ (a b : ιSTLC Tm (Γ , A)) → elim𝔹 false a b ≡ b 


  ιSTLC-is-set : ∀ i a → is-set (ιSTLC i a)

vz : ιSTLC Tm ((Γ , A) , A)
vz = q Id

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


-- p_∘⟨_,_⟩ : ∀ (δ : Hom Γ (Δ , A)) (γ : Hom Γ Δ) (a : ιSTLC Tm (Γ , A)) → p δ ∘s ⟨ γ , a ⟩ ≡ γ
-- p δ ∘⟨ γ , a ⟩ = {!   !} -- ⟨ p (p Sid) , q (p id) ⟩ ∘ ⟨ γ , a ⟩ === ⟨ p (p id) ∘ ⟨ γ , a ⟩ , q (pid) [ ⟨ γ , a ⟩ ] ⟩

∘↑  : (f : Hom Δ Ψ)
      (g : Hom Γ Δ) →
      (f ∘s g ↑ A) ≡ (f ↑ A) ∘s (g ↑ A)
∘↑ f g = sym (⟨ f ∘s p Sid , q Sid ⟩ ∘s ⟨ g ∘s p Sid , q Sid ⟩ 
                  ≡⟨ {!   !} ⟩
              ⟨ f ∘s (p Sid ∘s ⟨ g ∘s p Sid , q Sid ⟩) , q Sid ⟩
                  ≡⟨ {!   !} ⟩
              ⟨ f ∘s (g ∘s p Sid) , q Sid ⟩
                  ≡⟨ ap ⟨_, q Sid ⟩ (Sassoc f g (p Sid)) ⟩
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
ιSTLC-model .STLC.𝓒-strict = Ctx-is-set
ιSTLC-model .STLC.𝓒-term = SubsTerminal
ιSTLC-model .STLC.Ty = Ty
ιSTLC-model .STLC.𝕋 = ι𝕋
ιSTLC-model .STLC.extend = extend
ιSTLC-model .STLC.extension Γ A = to-natural-iso the-iso 
  where the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ (ι𝕋 A)) Hom[-, Γ , A ] 
        the-iso .make-natural-iso.eta Γ (γ , a) = ⟨ γ , a ⟩
        the-iso .make-natural-iso.inv Γ γ = p γ , q γ
        the-iso .make-natural-iso.eta∘inv Γ = funext pqη
        the-iso .make-natural-iso.inv∘eta Γ = funext λ x i → p⟨ x .fst ,  x .snd ⟩ i , q⟨ x .fst ,  x .snd ⟩ i
        the-iso .make-natural-iso.natural Γ Δ γ = funext (λ x → ⟨ x .fst , x .snd ⟩∘ γ) 


ιSTLC-lam-model : STLC-lamβη (ιSTLC-model)
ιSTLC-lam-model .STLC-lamβη._⇒_ = _⇒_
ιSTLC-lam-model .STLC-lamβη.lamβη = to-natural-iso the-iso
  where open STLC ιSTLC-model using (Tm[-⊕_,_] ; 𝕋)
        the-iso : make-natural-iso Tm[-⊕ A , B ] (𝕋 (A ⇒ B))
        the-iso .make-natural-iso.eta Γ = lam
        the-iso .make-natural-iso.inv Γ = app
        the-iso .make-natural-iso.eta∘inv Γ = funext lamη
        the-iso .make-natural-iso.inv∘eta Γ = funext appβ
        the-iso .make-natural-iso.natural Γ Δ γ = funext λ x → lam[] x γ

ιSTLC-Bool-model : STLC-Bool (ιSTLC-model)
ιSTLC-Bool-model .STLC-Bool.𝔹 = 𝔹
ιSTLC-Bool-model .STLC-Bool.tru = true
ιSTLC-Bool-model .STLC-Bool.fls = false
ιSTLC-Bool-model .STLC-Bool.elim = elim𝔹
ιSTLC-Bool-model .STLC-Bool.elim-tru = elimT _ _
ιSTLC-Bool-model .STLC-Bool.elim-fls = elimF _ _


ιSTLC-LamBool-model : STLC-lam-bools {lzero} {lzero} .fst .Precategory.Ob
ιSTLC-LamBool-model = (ιSTLC-model , ιSTLC-lam-model) , (ιSTLC-model , ιSTLC-Bool-model) , refl

open import Cat.Diagram.Initial
open import Cat.Diagram.Terminal

ιSLB-is-initial : Initial (STLC-lam-bools .fst)
ιSLB-is-initial .Initial.bot = ιSTLC-LamBool-model
ιSLB-is-initial .Initial.has⊥ x = contr the-hom {!   !}
  where 
        module SL = STLC-lamβη (x .fst .snd)
        module SB = STLC-Bool (x .snd .fst .snd)
        open Terminal
        open Functor
        open _=>_ 
        module S = STLC (x .fst .fst)
        module C = Precategory (S.𝓒)

        ιTy : Ty → S.Ty
        ιTy 𝔹 = transp (λ i → x .snd .snd (~ i) .STLC.Ty) i0 SB.𝔹
        ιTy (A ⇒ B) = SL._⇒_ (ιTy A) (ιTy B)

        ιCtx : Ctx → C.Ob
        ιCtx ε = S.ε
        ιCtx (Γ , A) = (ιCtx Γ) S.⊕ (ιTy A)

        ιSub : ιSTLC Sub (Γ , Δ) → C.Hom (ιCtx Γ) (ιCtx Δ)
        ιTm : ∀ {Γ} {A} → ιSTLC Tm (Γ , A) → S.Tm (ιTy A) (ιCtx Γ)
       

        ιSub ιSTLC.Id = C.id
        ιSub (Comp f g) = ιSub f C.∘ ιSub g
        ιSub (lid x i) = C.idl (ιSub x) i
        ιSub (rid x i) = C.idr (ιSub x) i
        ιSub (Sassoc f g h i) = C.assoc (ιSub f) (ιSub g) (ιSub h) i
        ιSub {Γ = Γ} ⟨⟩ = S.⟨⟩ (ιCtx Γ)
        ιSub (⟨⟩! f i) = S.⟨⟩! (ιSub f) i
        ιSub (⟨ γ , t ⟩) = S.⟨ ιSub γ , ιTm t ⟩
        ιSub (p γ) = S.p (ιSub γ)
        ιSub (p⟨_,_⟩ γ a i) = S.p⟨ ιSub γ , ιTm a ⟩ i
        ιSub (pqη γ i) = S.pqη (ιSub γ) i
        ιSub ((⟨ γ , t ⟩∘ δ) i) = (S.⟨ ιSub γ , ιTm t ⟩∘ ιSub δ) i
        ιSub (ιSTLC-is-set .Sub (Γ , Δ) γ δ P Q i j) = C.Hom-set (ιCtx Γ) (ιCtx Δ) (ιSub γ) (ιSub δ)
                                                           (λ i → ιSub (P i)) (λ i → ιSub (Q i))
                                                           i j

        ιTm = {!   !}

        the-hom : Precategory.Hom (STLC-lam-bools .fst) ιSTLC-LamBool-model x
        the-hom .fst .fst .STLC-Functor.F .Functor.F₀ = ιCtx
        the-hom .fst .fst .STLC-Functor.F .Functor.F₁ = ιSub
        the-hom .fst .fst .STLC-Functor.F .Functor.F-id = {!   !}
        the-hom .fst .fst .STLC-Functor.F .Functor.F-∘ = {!   !}
        the-hom .fst .fst .STLC-Functor.pres-⊤ = {!   !}
        the-hom .fst .fst .STLC-Functor.Fty = {!   !}
        the-hom .fst .fst .STLC-Functor.F𝕋 = {!   !}
        the-hom .fst .snd = {!   !}
        the-hom .snd = {!   !}  
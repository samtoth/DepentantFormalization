{-# OPTIONS --allow-unsolved-metas #-}
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

data Ctx {ℓ} (ty : Type ℓ) : Type ℓ where
  ε   : Ctx ty
  _,_ : Ctx ty → ty → Ctx ty

variable
  ℓ : Level
  ty : Type ℓ
  Γ Δ Ψ Φ : Ctx ty
  A B C : ty

,-inj : Path (Ctx ty) (Γ , A) (Δ , B) → (Γ ≡ Δ) × (A ≡ B)
,-inj {A = A} {B = B} x = ap (fst ∘ un, (ε , A)) x , ap (snd ∘ un, (ε , B)) x
  where un, : Ctx ty × ty → Ctx ty → Ctx ty × ty
        un, a ε = a
        un, a (x , x') = x , x'


open import Data.List
Ctx≃List : Ctx ty ≃ List ty
Ctx≃List = Iso→Equiv (to , iso from tofrom fromto)
  where to : _
        to ε = []
        to (Γ , A) = A ∷ to Γ
        from : _
        from [] = ε
        from (A ∷ Γ) = from Γ , A
        tofrom : _
        tofrom [] = refl
        tofrom (A ∷ Γ) = ap₂ _∷_ refl (tofrom Γ)
        fromto : _
        fromto ε = refl
        fromto (Γ , A) i = fromto Γ i , A

Ctx-discrete : Discrete ty → Discrete (Ctx ty)
Ctx-discrete d = transp (λ i → Discrete (ua Ctx≃List (~ i))) i0 decide
  where decide : _
        decide [] [] = yes refl
        decide [] (x ∷ b) = no (∷≠[] ∘ sym)
        decide (x ∷ a) [] = no ∷≠[]
        decide (x ∷ a) (y ∷ b) with d x y | decide a b
        ... | yes p | yes a₁ = yes (λ i → p i ∷ a₁ i)
        ... | yes p | no ¬a = no (¬a ∘ ∷-tail-inj)
        ... | no ¬a | ps = no (¬a ∘ ∷-head-inj)

Ctx-is-set : ∀ {ℓ} {ty : Type ℓ} → is-set ty → is-set (Ctx ty)
Ctx-is-set {ℓ} {ty} d = transp (λ i → is-set (ua (Ctx≃List {ℓ} {ty}) (~ i))) i0 (ListPath.is-set→List-is-set d)


CtxF : ∀ {ℓ} → Functor (Sets ℓ) (Sets ℓ)
CtxF = record { F₀ = λ t →  el (Ctx ∣ t ∣) (Ctx-is-set (t .is-tr))
              ; F₁ = F1
              ; F-id = funext Fid 
              ; F-∘ = λ f g → funext λ x → F∘ f g x 
              }
  where F1 : (A → B) → Ctx A → Ctx B
        F1 = λ { f ε → ε
               ; f (Γ , x) → F1 f Γ , f x }
        Fid : ∀ (x : Ctx A) → F1 id x ≡ x
        Fid ε = refl
        Fid (Γ , x) = λ i → (Fid Γ i) , x
        
        F∘ : ∀ (f : B → C) (g : A → B) x → F1 (f ∘ g) x ≡ F1 f (F1 g x)
        F∘ f g ε = refl
        F∘ f g (Γ , A) i = (F∘ f g Γ i) , f (g A)


data Els {ℓ₁ ℓ₂} {ty : Type ℓ₁} (el : ty → Type ℓ₂) : (Γ : Ctx ty) → Type (ℓ₁ ⊔ ℓ₂) where
  ! : Els el ε
  _⊕_ : {Γ : Ctx ty} {A : ty} → Els el Γ → el A → Els el (Γ , A)

qEls : ∀ {el : ty → Type ℓ} → Els el (Γ , A) → el A
qEls (_ ⊕ e) = e

pEls : ∀ {el : ty → Type ℓ} → Els el (Γ , A) → Els el Γ
pEls (γ ⊕ _) = γ

mapEls : {el₁ el₂ : ty → Type ℓ} → (∀ {ty} → el₁ ty → el₂ ty) → Els el₁ Γ → Els el₂ Γ
mapEls f ! = !
mapEls f (s ⊕ x) = mapEls f s ⊕ f x

data Var {ℓ} {ty : Type ℓ} : Ctx ty → ty → Type ℓ where
  vz : ∀ {Γ} {A} → Var (Γ , A) A
  vs : ∀ {Γ} {A} {B} → Var Γ A → Var (Γ , B) A
  
-- Variables are also decidable

VCode : Var Γ A → Var Γ A → Type ℓ
VCode {Γ = Γ , B} {B} vz v' = {! v'  !}
VCode (vs v) vz = Lift _ ⊥
VCode (vs v) (vs v') = VCode v v' 

vs-inj : ∀ {v v' : Var Γ A} → vs v ≡ vs v' → v ≡ v'
vs-inj = {!   !}

_≟V_ : ∀ (v v' : Var Γ A) → Dec (v ≡ v')
_≟V_ {Γ} {A} = {!   !} 


Ren : ∀ {ℓ} {ty : Type ℓ} (A B : Ctx ty) → Type ℓ
Ren Γ Δ = Els (Var Γ) Δ

wk1Ren : Ren Γ Δ → Ren (Γ , A) Δ
wk1Ren ! = !
wk1Ren (γ ⊕ x) = wk1Ren γ ⊕ vs x

wk2Ren : Ren Γ Δ → Ren (Γ , A) (Δ , A)
wk2Ren x = (wk1Ren x) ⊕ vz

idRen : Ren Γ Γ
idRen {Γ = ε} = !
idRen {Γ = Γ , x} = wk2Ren idRen



_[_]v : Var Γ A → Ren Δ Γ → Var Δ A
vz [ _ ⊕ x ]v = x
vs v [ γ ⊕ x ]v = v [ γ ]v

_[id]v : (v : Var Γ A) → v [ idRen ]v ≡ v
vz [id]v = refl
vs v [id]v = {!   !}


Ren∘ : ∀ {Γ Δ Σ : Ctx ty} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
Ren∘ ! δ = !
Ren∘ (γ ⊕ x) δ = (Ren∘ γ δ) ⊕ (x [ δ ]v)

wk2∘ : ∀ {Γ Δ Σ} {A : ty} (γ : Ren Δ Σ) (δ : Ren Γ Δ) → wk2Ren {A = A} (Ren∘ γ δ) ≡ Ren∘ (wk2Ren γ) (wk2Ren δ)
wk2∘ γ δ  = {!   !}

wk1η : ∀ {Γ Δ Σ} {A : ty} → (γ : Ren Δ Σ) (f : Ren Γ Δ) (x : Var Γ A) → Ren∘ (wk1Ren γ) (f ⊕ x) ≡ Ren∘ γ f 
wk1η γ f x = {!   !}

idrRen : ∀ (f : Ren Γ Δ) → Ren∘ f idRen ≡ f
idrRen ! = refl
idrRen (f ⊕ x) = λ i → (idrRen f i) ⊕ (x [id]v) i

idlRen : ∀ (f : Ren Γ Δ) → Ren∘ idRen f ≡ f
idlRen ! = refl
idlRen (f ⊕ x) = λ i → (wk1η _ _ x ∙ idlRen f) i ⊕ x

Rens : ∀ (ty : Type ℓ) → Precategory _ _
Rens ty .Precategory.Ob = Ctx ty
Rens _ .Precategory.Hom = Ren
Rens _ .Precategory.Hom-set = {!   !}
Rens _ .Precategory.id = idRen
Rens _ .Precategory._∘_ = Ren∘
Rens _ .Precategory.idr = idrRen
Rens _ .Precategory.idl = idlRen
Rens _ .Precategory.assoc = {!   !}

RensTerminal : ∀ {ty : Type ℓ} → Terminal (Rens ty)
RensTerminal .Terminal.top = ε
RensTerminal .Terminal.has⊤ = λ x → contr ! (λ { ! → refl})



extendRens : ty → Functor (Rens ty) (Rens ty)
extendRens A .Functor.F₀ Γ = Γ , A
extendRens A .Functor.F₁ = wk2Ren
extendRens A .Functor.F-id = refl
extendRens A .F-∘ f g = wk2∘ f g



module _ {o ℓ} {ty : Type o} (T : Ctx ty → ty → Type ℓ) where
  Subst : (A B : Ctx ty) → Type (o ⊔ ℓ)
  Subst Γ Δ = Els (T Γ) Δ

  Ren→Subst : (f : ∀ {Γ} {A} → Var Γ A → T Γ A) → (∀ {Γ Δ} → Ren Γ Δ → Subst Γ Δ)
  Ren→Subst f ! = !
  Ren→Subst f (γ ⊕ x) = (Ren→Subst f γ) ⊕ (f x) 
    
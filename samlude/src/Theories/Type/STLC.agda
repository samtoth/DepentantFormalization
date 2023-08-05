{-# OPTIONS --cubical #-}
module Theories.Type.STLC where

open import Foundations.Prelude
open import Foundations.Equiv
open import Foundations.Homotopy

open import Categories.Category
open import Categories.TYPE
open import Categories.Diagram.Zero

open import Categories.Functor
open import Categories.Functor.Good

open Functor
open IsCategory {{...}}
open Good {{...}}

open Terminal {{...}}
open Initial {{...}}

open import Categories.Diagram.Two

open HasProducts {{...}}

Fam : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
Category.Ob (Fam {ℓ}) = Σ     (Type ℓ)
                        λ X → X → (Type ℓ)
Category.Hom Fam (I , A) (J , B) = Σ    (I → J)
                                   λ f → ∀ {i : I} → A i → B (f i)

instance
  FamCat : ∀ {ℓ} → IsCategory (Fam {ℓ})
  IsCategory.Id FamCat = Id , Id
  IsCategory._∘_ FamCat f g = (f .fst ∘ g .fst) , (f .snd ∘ g .snd)

record CwF (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    𝓒 : Category ℓ ℓ'
    {{𝓒cat}} : IsCategory 𝓒

  open Category 𝓒 renaming (Ob to Ctx ; Hom to Subst) public

  field
    {{𝓒ter}} :  Terminal 𝓒

  ⟨⟩ : ∀ {Γ} → Subst Γ (⊤ {ℓ})
  ⟨⟩ = !

  field
    𝕋 : Functor (𝓒 ^op) (Fam {ℓ})

  field
    {{𝕋good}} : Good 𝕋


  Ty : Ctx → Type ℓ
  Ty Γ = 𝕋 .F0 Γ .fst

  _[_]ty : ∀ {Γ Δ} → Ty Γ → Subst Δ Γ → Ty Δ
  _[_]ty A γ = 𝕋 .F1 (sym γ) .fst A

  Tm : (Γ : Ctx) → (A : Ty Γ) → Type ℓ
  Tm Γ = 𝕋 .F0 Γ .snd

  _[_] : ∀ {Γ Δ A} → Tm Γ A → (γ : Subst Δ Γ) → Tm Δ (A [ γ ]ty)
  a [ γ ] = 𝕋 .F1 (sym γ) .snd a

  field
    _∷_ : (Γ : Ctx) → (A : Ty Γ) → Ctx

    p : ∀ {Γ} {A} → Subst (Γ ∷ A) Γ
    q : ∀ {Γ} {A} → Tm (Γ ∷ A) (A [ p ]ty)

    ⟨_,_⟩     : ∀ {Γ Δ A} → (γ : Subst Δ Γ) → (a : Tm Γ A) → Subst Δ (Γ ∷ A)

    p∘⟨-,-⟩   : ∀ {Γ Δ} {A : Ty Γ} {γ : Subst Δ Γ} {a : Tm Γ A} → p ∘ ⟨ γ , a ⟩ ≡ γ

  -- sublem : ∀ {A B C} {f : B → C} {g : A → B} {a} → f (g a) ≡ (f ∘ g) a -- Holds definitionally

  lem : ∀ {Γ Δ Ψ} {A : Ty Γ} {γ : Subst Δ Γ} {δ : Subst Ψ Δ} → ((A [ γ ]ty) [ δ ]ty) ≡ (A [ γ ∘ δ ]ty)
  lem {Γ} {Δ} {Ψ} {A} {γ} {δ} i = distrib ⦃ r = 𝕋good ⦄ {f = sym δ} {sym γ} (~ i) .fst A

  lem2 : ∀ {Γ Δ} {A : Ty Γ} {γ : Subst Δ Γ} {a : Tm Γ A} → Path (Ty Δ) ((A [ p ]ty) [ ⟨ γ , a ⟩ ]ty) (A [ γ ]ty)
  lem2 {Γ} {Δ} {A} {γ} {a} = (λ i → A [ p∘⟨-,-⟩ {γ = γ} {a} i ]ty) ∙ lem

  field
    q[⟨-,-⟩]  : ∀ {Γ Δ} {A : Ty Γ} {γ : Subst Δ Γ} {a : Tm Γ A} → PathP (λ i → Tm Δ (lem2 {γ = γ} {a} i)) (q [ ⟨ γ , a ⟩ ]) (a [ γ ])

open import Data.Nat

record UCwF (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cwf : CwF ℓ ℓ'

  open CwF cwf public

  field
    Tycontr : ∀ {Γ} → isContr (Ty Γ)

  * : ∀ {Γ} → Ty Γ
  * = Tycontr .fst

  subable : ∀ {Γ : Ctx} (a b : Ty Γ) → a ≡ b
  subable a b = trust
    where postulate trust : a ≡ b

  extend : ∀ {Γ} → Tm Γ * → Subst Γ (Γ ∷ *)
  extend {Γ} a = transp (λ i → Subst Γ (Γ ∷ subable {Γ} * * i)) i0 ⟨ Id , a ⟩

  _[_]* : ∀ {Γ Δ} → Tm Γ * → (γ : Subst Δ Γ) → Tm Δ *
  _[_]* {Γ} {Δ} x γ = transp (λ i → Tm Δ (subable (* [ γ ]ty) * i)) i0 (x [ γ ])

  q* : ∀ {Γ} → Tm (Γ ∷ *) *
  q* {Γ} = transp (λ i → Tm (Γ ∷ *) (subable (* [ p ]ty) * i)) i0 q

record ƛ-UCwF (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ucwf : UCwF ℓ ℓ'

  open UCwF ucwf public

  field
    lam : ∀ {Γ} → Tm (Γ ∷ *) * → Tm Γ *
    app : ∀ {n} → Tm n * → Tm n * → Tm n *



  field
    -- subApp : ...
    -- subLam : ...

    β : ∀ {n} {f : Tm (n ∷ *) *} {a : Tm n *} → Path (Tm n *) (app (lam f) a) (f [ extend a ]*)
    η : ∀ {Γ} {t : Tm Γ *} → Path (Tm Γ *) (lam (app (t [ p ]*) q*)) t


module Initial-ƛUCwF where
  open Category

  open import Categories.Category.Free
  open import Categories.Diagram.Base
  open Limit

  data Term : ℕ → Type
  data Subst : ℕ → ℕ → Type

  variable
    m n k : ℕ

  PreSubsts : Category ℓ-zero ℓ-zero
  PreSubsts = Free ℕ Subst

  data SubstsLaws : ℕ → ℕ → Type

  Substs : Category ℓ-zero ℓ-zero
  Substs = Cat ℕ SubstsLaws



  data PreTerm : ℕ → Type where
    q    : PreTerm (suc n)
    _[_] : Term n → Substs .Hom m n → PreTerm m
    lam  : Term (suc n) → PreTerm n
    app  : Term n → Term n → PreTerm n


  data Subst where
    ⟨⟩ : Subst n zero
    ⟨_,_⟩ : Substs .Hom m n → Term n → Subst m (suc n)
    p   : Subst (suc n) n

    -- p∘⟨-,-⟩ : ∀ {Γ Δ} {γ : Subst Δ Γ} {a : Term Γ} → {!Special p ∘ Special ⟨ Special γ , a ⟩ ≡ Special γ!} -- p ∘ ⟨ Special γ , a ⟩ ≡ γ

  data SubstsLaws where
    sub : ∀ {m n} → PreSubsts .Hom m n → SubstsLaws m n

    p∘⟨-,-⟩ : ∀ {Γ Δ} {γ : Substs .Hom Δ Γ} {a : Term Γ} → sub (Special p ∘ Special ⟨ γ , a ⟩) ≡ γ

  instance
    SubstsCat : IsCategory Substs
    IsCategory.Id SubstsCat = sub Id
    IsCategory._∘_ SubstsCat (sub f) (sub g) = sub (f ∘ g)

  data Term where
    t : ∀ {n} → PreTerm n → Term n

    q[⟨-,-⟩] : ∀ {Γ Δ} {γ : Substs .Hom Δ Γ} {a : Term Γ} → Path (Term Δ) (t ((t q) [ sub (Special ⟨ γ , a ⟩) ])) (t (a [ γ ]))

    -[Id] : ∀ {Γ} {a : Term Γ} → Path (Term Γ) (t ( a [ sub Id ])) a
    -[][] : ∀ {Γ Δ Ψ} {γ : Substs .Hom Δ Γ} {δ : Substs .Hom Ψ Δ} {a : Term Γ} → Path (Term Ψ) (t ((t (a [ γ ])) [ δ ])) (t (a [ (γ ∘ δ) ]))


  instance
    SubstsTerminal : Terminal Substs
    HasLimit.lim (Terminal.haslim SubstsTerminal) = record { apex = zero ; arrows = λ ()}
    HasLimit.lim-initial (Terminal.haslim SubstsTerminal) x = sub (Special ⟨⟩)


  T : Functor (Substs ^op) Fam
  T = swapOp' (record { F0 = λ n → ⊤ , (λ _ → Term n)
                      ; F1 = λ γ → sym ( (λ x → x) , (λ x → t (x [ γ ])))
                      })

  Tgood : Good T
  Good.id Tgood = λ i → (λ x → x) , λ x → -[Id] i
  Good.distrib Tgood {f = f} {g} i = {!!}

  lamcwf : ƛ-UCwF ℓ-zero ℓ-zero
  CwF.𝓒 (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = Substs
  CwF.𝓒cat (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = _
  CwF.𝓒ter (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = SubstsTerminal
  CwF.𝕋 (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = T
  CwF.𝕋good (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = Tgood
  CwF._∷_ (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = λ Γ _ → suc Γ
  CwF.p (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = sub (Special p)
  CwF.q (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = t q
  CwF.⟨_,_⟩ (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = λ γ a → sub (Special ⟨ γ , a ⟩)
  CwF.p∘⟨-,-⟩ (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = p∘⟨-,-⟩
  CwF.q[⟨-,-⟩] (UCwF.cwf (ƛ-UCwF.ucwf lamcwf)) = q[⟨-,-⟩]
  UCwF.Tycontr (ƛ-UCwF.ucwf lamcwf) = {!!} -- terminal TYPE is contr
  ƛ-UCwF.lam lamcwf = t ∘ lam
  ƛ-UCwF.app lamcwf = λ f x → t (app f x)
  ƛ-UCwF.β lamcwf = {!!}
  ƛ-UCwF.η lamcwf = {!!}

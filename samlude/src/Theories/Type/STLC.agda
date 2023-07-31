{-# OPTIONS --cubical #-}
module Theories.Type.STLC where

open import Foundations.Prelude
open import Foundations.Equiv
open import Foundations.Homotopy

open import Categories.Category
open import Categories.TYPE
open import Categories.Diagram.Zero

open import Categories.Functor

open Functor
open IsCategory {{...}}

open Terminal {{...}}
open Initial {{...}}

open import Categories.Diagram.Two

open HasProducts {{...}}

Fam : ∀ {ℓ} → Category (ℓ-suc ℓ) ℓ
Category.Ob (Fam {ℓ}) = Σ     (Type ℓ)
                        λ X → X → (Type ℓ)
Category.Hom Fam (I , A) (J , B) = Σ    (I → J)
                                   λ f → ∀ {i : I} → A i → B (f i)

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
    T : Functor (𝓒 ^op) (Fam {ℓ})

  Ty : Ctx → Type ℓ
  Ty Γ = T .F0 Γ .fst

  _[_]ty : ∀ {Γ Δ} → Ty Γ → Subst Δ Γ → Ty Δ
  _[_]ty A γ = T .F1 (sym γ) .fst A

  Tm : (Γ : Ctx) → (A : Ty Γ) → Type ℓ
  Tm Γ = T .F0 Γ .snd

  _[_] : ∀ {Γ Δ A} → Tm Γ A → (γ : Subst Δ Γ) → Tm Δ (A [ γ ]ty)
  a [ γ ] = T .F1 (sym γ) .snd a

  field
    _∷_ : (Γ : Ctx) → (A : Ty Γ) → Ctx

    p : ∀ {Γ} {A} → Subst (Γ ∷ A) Γ
    q : ∀ {Γ} {A} → Tm (Γ ∷ A) (A [ p ]ty)

    ⟨_,_⟩     : ∀ {Γ Δ A} → (γ : Subst Δ Γ) → (a : Tm Γ A) → Subst Δ (Γ ∷ A)

    p∘⟨-,-⟩   : ∀ {Γ Δ} {A : Ty Γ} {γ : Subst Δ Γ} {a : Tm Γ A} → p ∘ ⟨ γ , a ⟩ ≡ γ
    q[⟨-,-⟩]  : ∀ {Γ Δ A} {γ : Subst Δ Γ} {a : Tm Γ A} → PathP (λ i → {!Tm Δ (A [ p∘⟨-,-⟩ i ]ty)!}) (q [ ⟨ γ , a ⟩ ]) (a [ γ ])

-- open import Data.Nat

-- record UCwF (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
--   field
--     cwf : CwF ℓ ℓ'

--   open CwF cwf public

--   field
--     Tycontr : ∀ {Γ} → isContr (Ty Γ)

--   * : ∀ {Γ} → Ty Γ
--   * = Tycontr .fst

--   subable : ∀ {Γ : Ctx} {a b : Ty Γ} → a ≡ b
--   subable = (λ ()) bot
--     where postulate bot : ⊥

--   extend : ∀ {Γ} → Tm Γ * → Subst Γ (Γ ∷ *)
--   extend {Γ} a = transp (λ i → Subst Γ (Γ ∷ subable i)) i0 ⟨ Id , a ⟩

--   _[_]* : ∀ {Γ Δ} → Tm Γ * → (γ : Subst Δ Γ) → Tm Δ *
--   x [ γ ]* = transp (λ i → Tm _ (subable i)) i0 (x [ γ ])

--   q* : ∀ {Γ} → Tm (Γ ∷ *) *
--   q* {Γ} = transp (λ i → Tm (Γ ∷ subable i) (subable i)) i0 q

-- record ƛ-UCwF (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
--   field
--     ucwf : UCwF ℓ ℓ'

--   open UCwF ucwf public

--   field
--     lam : ∀ {Γ} → Tm (Γ ∷ *) * → Tm Γ *
--     app : ∀ {n} → Tm n * → Tm n * → Tm n *



--   field
--     -- subApp : ...
--     -- subLam : ...

--     β : ∀ {n} {f : Tm (n ∷ *) *} {a : Tm n *} → Path (Tm n *) (app (lam f) a) (f [ extend a ]*)
--     η : ∀ {Γ} {t : Tm Γ *} → Path (Tm Γ *) (lam (app (t [ p ]*) q*)) t


-- module Initial-ƛUCwF where
--   data Subst : ℕ → ℕ → Type
--   data Term : ℕ → Type

--   variable
--     m n k : ℕ

--   data Term where
--     q    : Term (suc n)
--     _[_] : Term n → Subst m n → Term m
--     lam  : Term (suc n) → Term n
--     app  : Term n → Term n → Term n

--   data Subst where
--     ⟨⟩ : Subst n zero
--     ⟨_,_⟩ : Subst m n → Term m → Subst m (suc n)
--     p   : Subst (suc n) n

--   open import Categories.Category.Free
--   open import Categories.Diagram.Base
--   open Limit

--   Substs : Category ℓ-zero ℓ-zero
--   Substs = Free ℕ Subst

--   instance
--     SubstsTerminal : Terminal Substs
--     HasLimit.lim (Terminal.haslim SubstsTerminal) = record { apex = zero ; arrows = λ ()}
--     HasLimit.lim-initial (Terminal.haslim SubstsTerminal) x = Special ⟨⟩


  -- T : Functor (Substs ^op) Fam
  -- fst (F0 T Γ) = ⊤ -- well formed types at context Γ - unityped
  -- snd (F0 T Γ) _ = Term Γ  -- Well formed terms of type A at Γ (A is trivial)

  -- F1 T (sym FreeId) = Id
  -- F1 T (sym (FreeComp f g)) = {!T .F1!}
  -- F1 T (sym (idL x i)) = {!!}
  -- F1 T (sym (idR x i)) = {!!}

  -- F1 T (sym (Special x)) = {!!}

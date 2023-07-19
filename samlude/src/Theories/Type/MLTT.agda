{-# OPTIONS --cubical --cumulativity #-}
module Theories.Type.MLTT {ℓ} where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor
open import Categories.TYPE
open import Categories.Diagram.Zero
open import Categories.FUNCTORS

open Category {{...}}
open IsCategory {{...}} renaming (Id to id)
open Functor

data Ctx   : Type ℓ
data Ty    : Ctx → Type ℓ
data Tm    : (Γ : Ctx) → Ty Γ → Type ℓ
data Subst : Ctx → Ctx → Type ℓ
data Var   : (Γ : Ctx) → Ty Γ → Type ℓ

data Ctx where
  ε : Ctx
  _,_ : (Γ : Ctx) → Ty Γ → Ctx


data Ty where
  U    : ∀ {Γ} → Ty Γ
  El   : ∀ {Γ} → Tm Γ U → Ty Γ
  pi   : ∀ {Γ} → (A : Ty Γ) → (B : Ty (Γ , A)) → Ty Γ
  nat  : ∀ {Γ} → Ty Γ
  _[_] : ∀ {Γ} {Δ} → Ty Γ → Subst Δ Γ → Ty Δ



data Subst where
  Id   : ∀ {Γ} → Subst Γ Γ
  Eps  : ∀ {Γ} → Subst Γ ε
  Comp : ∀ {Γ Δ Σ} → Subst Δ Σ → Subst Γ Δ → Subst Γ Σ
  Wk   : ∀ {Γ} {Δ} (A : Ty Δ) → (σ : Subst Γ Δ) → Subst (Γ , A [ σ ]) (Δ , A)
  Lft  : ∀ {Γ} {A : Ty Γ} → Subst (Γ , A) Γ
  Ext  : ∀ {Γ Δ} (σ : Subst Γ Δ) → {A : Ty Δ} → Tm Γ (A [ σ ]) → Subst Γ (Δ , A)

  idr   : ∀ {Γ} {Δ} → (ƛ : Subst Γ Δ) → Comp ƛ Id ≡ ƛ
  idl   : ∀ {Γ} {Δ} → (ρ : Subst Γ Δ) → Comp Id ρ ≡ ρ


data Var where
  vhere  : ∀ {Γ} {A : Ty Γ} → Var (Γ , A) (A [ Lft ])
  vthere : ∀ {Γ} {A : Ty Γ} {B : Ty Γ} → Var Γ A → Var (Γ , B) (A [ Lft ])

data Tm where
  _[_]ₜ : ∀ {Γ Δ} {A : Ty Δ} → Tm Δ A → (σ : Subst Γ Δ) → Tm Γ (A [ σ ])

  var : ∀ {Γ} {A} → Var Γ A → Tm Γ A
  lam : ∀ {Γ} {A} {B} → Tm (Γ , A) B → Tm Γ (pi A B)
  app : ∀ {Γ} {A} {B} → Tm Γ (pi A B) → (a : Tm Γ A) → Tm Γ (B [ Ext Id (a [ Id ]ₜ) ])

  zero : ∀ {Γ} → Tm Γ nat
  suc  : ∀ {Γ} → Tm Γ (pi nat nat)




𝓒 : Category ℓ ℓ
𝓒 = Cat Ctx Subst

𝓒Presheaf : Type (ℓ-suc ℓ)
𝓒Presheaf = Functor (𝓒 ^op) (TYPE ℓ)

record FamPSh (Γ : 𝓒Presheaf) : Type (ℓ-suc ℓ) where
  field
    AI : ∀ {I : (𝓒 ^op) .Ob } → Γ .F0 I → Type ℓ
    Af : ∀ {I J} {f : (𝓒 ^op) .Hom I J} → (α : Γ .F0 I) → (TYPE ℓ) .Hom (AI α) (AI (Γ .F1 f α))


open Terminal {{...}}

⟦_⟧ : Ctx → 𝓒Presheaf
F0 ⟦ Γ ⟧ Δ = {!!}
F1 ⟦ Γ ⟧ (sym σ) A = {!!}

⟦_⊢_⟧ : (Γ : Ctx) → (A : Ty Γ) → FamPSh ⟦ Γ ⟧
FamPSh.AI ⟦ Γ ⊢ A ⟧ = {!!}
FamPSh.Af ⟦ Γ ⊢ A ⟧ = {!!}


data Nf : (Γ : Ctx) → Ty Γ → Type ℓ
data Ne : (Γ : Ctx) → Ty Γ → Type ℓ
eval : ∀ Γ → (A : Ty Γ) → Nf Γ A → Tm Γ A


-- maximally reduced
data Nf where
  neuU  : ∀ {Γ} → Ne Γ U → Nf Γ U
  neuEl : ∀ {Γ} {A : Tm Γ U} → Ne Γ (El A) → Nf Γ (El A)
  lam   : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ , A)} → Nf (Γ , A) B → Nf Γ (pi A B)

-- stuck terms
data Ne where
  var : ∀ {Γ} {A : Ty Γ} → Var Γ A → Ne Γ A
  app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ , A)} → Ne Γ (pi A B) → (v : Nf Γ A) → Ne Γ (B [ Ext Id (eval Γ A v [ Id  ]ₜ)])


reify : ∀ Γ → (A : Ty Γ) → Tm Γ A → Nf Γ A
reify Γ = {!!}

evalNe : ∀ Γ → (A : Ty Γ) → Ne Γ A → Tm Γ A
evalNe Γ A (var x) = var x
evalNe Γ .(_ [ Ext Id (eval Γ _ v [ Id ]ₜ) ]) (app x v) = app (evalNe _ _ x) (eval _ _ v)

eval Γ .U (neuU x) = evalNe _ _ x
eval Γ .(El _) (neuEl x) = evalNe _ _ x
eval Γ .(pi _ _) (lam x) = lam (eval _ _ x)


normalise : ∀ Γ → (A : Ty Γ) → Tm Γ A → Tm Γ A
normalise Γ A = eval Γ A ∘ reify Γ A

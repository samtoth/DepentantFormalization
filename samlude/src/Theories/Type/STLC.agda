{-# OPTIONS --cubical #-}
module Theories.Type.STLC where

open import Foundations.Prelude

open import Foundations.Decidable
open import Categories.TYPE
open import Categories.Negation {𝓒 = TYPE ℓ-zero}
open import Categories.Diagram.Zero

open Terminal {{...}}
open Initial {{...}}

data Ty : Type where
  Bool : Ty
  _⇒_  : Ty → Ty → Ty

encodeB : Ty → Type
encodeB Bool = Ty
encodeB (B ⇒ B') = ⊥

_≟T_ : (A B : Ty) → Dec (A ≡ B)
Bool ≟T Bool = yes (λ i → Bool)
Bool ≟T (B ⇒ B₁) = no λ p → subst encodeB p Bool
(A ⇒ A₁) ≟T Bool = no (λ p → subst encodeB (λ i → p (~ i)) Bool )
(A ⇒ B) ≟T (A' ⇒ B') with A ≟T A' | B ≟T B'
... | yes pA | yes pB = yes (λ i → pA i ⇒ pB i)
... | yes pA | no ¬pB = no {!!}
... | no ¬pA | yes pB = no {!!}
... | no ¬pA | no ¬pB = no {!!}

infixr 40 _⇒_

data Ctx : Type where
  ε   : Ctx
  _,_ : Ctx → Ty → Ctx

variable
  Γ Δ Ψ Φ : Ctx
  A B C : Ty


data Term : Ctx → Ty → Type

data Subst : Ctx → Ctx → Type

variable
  γ γ' : Subst Γ Δ
  δ : Subst Δ Ψ
  ψ : Subst Ψ Φ

  a a' : Term Γ A

data Subst where
  SId   : Subst Γ Γ
  SComp : Subst Δ Ψ → Subst Γ Δ → Subst Γ Ψ

  lid   : SComp SId γ ≡ γ
  rid   : SComp γ SId ≡ γ
  assoc : SComp γ (SComp δ ψ) ≡ SComp (SComp γ δ) ψ


  ⟨⟩ : Subst Γ ε
  ⟨⟩! : ∀ (x : Subst Γ ε) → x ≡ ⟨⟩

  ⟨_,_⟩ : Subst Γ Δ → Term Γ A → Subst Γ (Δ , A)

  p : Subst (Γ , A) Γ
  p∘⟨-,-⟩ : ∀ {Γ Δ} {γ : Subst Δ Γ} {a : Term Δ A} → SComp p ⟨ γ , a ⟩ ≡ γ



  set : ∀ (p q : γ ≡ γ') → p ≡ q

data Term where
  q : Term (Γ , A) A

  _[_] : Term Γ A → Subst Δ Γ → Term Δ A

  [][] : (a [ γ ]) [ δ ] ≡ a [ SComp γ δ ]
  [Id] : a [ SId ] ≡ a

  q[⟨-,-⟩] : q [ ⟨ γ , a ⟩ ] ≡ a [ γ ]


  lam : Term (Γ , A) B → Term Γ (A ⇒ B)
  app : Term Γ (A ⇒ B) → Term Γ A → Term Γ B

  β   : (bod : Term (Γ , A) B) → (a : Term Γ A) → app (lam bod) a ≡ bod [ ⟨ SId , a ⟩ ]
  η   : (f : Term Γ (A ⇒ B)) → f ≡ lam (app (f [ p ]) q)

  true false : Term Γ Bool

  if_then_else : Term Γ Bool → Term Γ A → Term Γ A → Term Γ A

  ite-true  : if true then a else a' ≡ a
  ite-false : if false then a else a' ≡ a'

module examples where
  not : Term ε (Bool ⇒ Bool)
  not = lam (if q then false else true)

  nand : Term ε (Bool ⇒ Bool ⇒ Bool)
  nand = lam (if q then lam (if q then false else true) else (lam true))

data ValSort : Type where Ne Nf : ValSort

variable V : ValSort

data Val : ValSort → Ctx → Ty → Type where
  -- Terms in Normal form
  ne   : Val Ne Γ A → Val Nf Γ A
  lam  : Val Nf (Γ , A) B → Val Nf Γ (A ⇒ B)
  true false : Val Nf Γ Bool

  -- Neutral terms (terms that are stuck)
  app  : Val Ne Γ (A ⇒ B) → Val Nf Γ A → Val Ne Γ B
  wk   : Val Ne Γ A → Val Ne (Γ , B) A
  q    : Val Ne (Γ , A) A
  if_t_e : Val Ne Γ Bool → Val Nf Γ A → Val Nf Γ A → Val Ne Γ A

-- Embedding Vals into Terms -----------------------

⌜_⌝ : Val V Γ A → Term Γ A

-- normals

⌜ ne x ⌝ = ⌜ x ⌝
⌜ lam x ⌝ = lam ⌜ x ⌝
⌜ true ⌝ = true
⌜ false ⌝ = false

-- neutrals

⌜ app f x ⌝ = app ⌜ f ⌝ ⌜ x ⌝
⌜ wk x ⌝ = ⌜ x ⌝ [ p ]
⌜ q ⌝ = q
⌜ if cond t a e b ⌝ = if ⌜ cond ⌝ then ⌜ a ⌝ else ⌜ b ⌝

--------------------------------------------------

lemma : ∀ {a b : Val Ne Γ A} → ne a ≡ ne b → a ≡ b
lemma P = {!!}

_≟_ : ∀ (a b : Val V Γ A) → Dec (a ≡ b)

-- normals --------------------------------------------------------------------

encodeNe : Val Nf Γ A → Type
encodeNe {Γ} {A} (ne _) = Val Ne Γ A
encodeNe (lam _) = ⊥
encodeNe true = ⊥
encodeNe false = ⊥

encodeTr : Val Nf Γ Bool → Type
encodeTr (ne x) = ⊥
encodeTr (true {Γ}) = Val Nf Γ Bool
encodeTr false = ⊥

encodeF : Val Nf Γ Bool → Type
encodeF (ne x) = ⊥
encodeF true = ⊥
encodeF (false {Γ}) = Val Nf Γ Bool

encodeApp : Val Ne Γ A → Type
encodeApp (app {Γ} {A} {A'} f a) = Val Nf Γ A
encodeApp (wk x) = ⊥
encodeApp q = ⊥
encodeApp (if x t x₁ e x₂) = ⊥

encodeWk : Val Ne Γ A → Type
encodeWk (app _ _) = ⊥
encodeWk (wk {Γ} {A} _) = Val Ne Γ A
encodeWk q = ⊥
encodeWk (if _ t _ e _) = ⊥

encodeITE : Val Ne Γ A → Type
encodeITE (app _ _) = ⊥
encodeITE (wk _) = ⊥
encodeITE q = ⊥
encodeITE (if_t_e {Γ} _ _ _) = Val Ne Γ Bool

_≟_ {V = Nf} (ne a) (ne b) with a ≟ b
... | yes P = yes (λ i → ne (P i))
... | no ¬P = no λ p → ¬P (lemma p)
_≟_ {V = Nf} (ne x) (lam _) = no λ p → subst encodeNe p x
_≟_ {V = Nf} (ne x) true = no λ p → subst encodeNe p x
_≟_ {V = Nf} (ne x) false = no λ p → subst encodeNe p x

_≟_ {V = Nf} (lam a) (lam b) with a ≟ b
... | yes P = yes (λ i → lam (P i))
... | no ¬P = no λ p → {!!}
_≟_ {V = Nf} (lam a) (ne _) = no λ p → subst encode p a
  where encode : Val Nf Γ (A ⇒ B) → Type
        encode (ne x) = ⊥
        encode (lam {Γ} {A} {B} x) = Val Nf (Γ , A) B


_≟_ {V = Nf} true true = yes (λ i → true)
_≟_ {V = Nf} true (ne _) = no λ p → subst encodeTr p true
_≟_ {V = Nf} true false = no λ p → subst encodeTr p true

_≟_ {V = Nf} false false = yes (λ i → false)
_≟_ {V = Nf} false (ne _) = no λ p → subst encodeF p false
_≟_ {V = Nf} false true = no λ p → subst encodeF p false

-- neutrals -------------------------------------------------------------------

_≟_ {V = Ne} (app {Γ} {A} f a) (app {Γ} {A'} f' a') with A ≟T A'
... | no ¬p0  = no (λ x → {!!})
... | yes p0  = {!!}
_≟_ {V = Ne} (app _ a) (wk _) = no (λ p → subst encodeApp p a )
_≟_ {V = Ne} (app _ a) q = no (λ p → subst encodeApp p a)
_≟_ {V = Ne} (app _ a) (if b t b₁ e b₂) = no (λ p → subst encodeApp p a)


wk x ≟ wk y with x ≟ y
... | yes P = yes (λ i → wk (P i))
... | no ¬P = no {!!}

wk x ≟ app _ _ = no (λ p → subst encodeWk p x)
wk x ≟ q = no (λ p → subst encodeWk p x)
wk x ≟ if _ t _ e _ = no (λ p → subst encodeWk p x)

_≟_ q b = {!!}

if c t _ e _ ≟ app _ _ = no (λ p → subst encodeITE p c)
if c t _ e _ ≟ wk _ = no (λ p → subst encodeITE p c)
if c t _ e _ ≟ q = no (λ p → subst encodeITE p c)
if c t tr e f ≟ if c' t tr' e f' = {!!}



-- Normalization statements ---------------------------------------------------

norm : Term Γ A → Val Nf Γ A
norm = {!!}

complete : ∀ {t : Term Γ A} → t ≡ ⌜ norm t ⌝
complete = {!!}

sound : ∀ (t t' : Term Γ A) → t ≡ t' → norm t ≡ norm t'
sound = {!!}

stable : (n : Val Nf Γ A) → norm ⌜ n ⌝ ≡ n
stable = {!!}

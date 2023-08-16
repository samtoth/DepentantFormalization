{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Theories.Type.STLC.Vals where

open import Foundations.Prelude

open import Theories.Type.STLC.Syntax

open import Data.Fin

open import Foundations.Decidable
open import Categories.TYPE
open import Categories.Negation {𝓒 = TYPE ℓ-zero}
open import Categories.Diagram.Zero
open import Categories.Diagram.Two

open Terminal {{...}}
open Initial {{...}}
open HasProducts {{...}}


data ValKind : Type where Ne Nf : ValKind

variable V : ValKind

data Val : ValKind → Ctx → Ty → Type where
  -- Terms in Normal form
  ne   : Val Ne Γ A → Val Nf Γ A
  lam  : Val Nf (Γ , A) B → Val Nf Γ (A ⇒ B)
  wk   : Val Nf Γ A → Val Nf (Γ , B) A
  true false : Val Nf Γ Bool

  -- Neutral terms (terms that are stuck)
  app  : Val Ne Γ (A ⇒ B) → Val Nf Γ A → Val Ne Γ B
  q    : Val Ne (Γ , A) A
  if_then_else : Val Ne Γ Bool → Val Nf Γ A → Val Nf Γ A → Val Ne Γ A

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
⌜ if cond then a else b ⌝ = if ⌜ cond ⌝ then ⌜ a ⌝ else ⌜ b ⌝

--------------------------------------------------

-- Injectivity of Val constructors

ne-inj : ∀ {a b} → ne a ≡ ne b → a ≡ b
ne-inj = {!!}

lam-inj : ∀ {a b : Val Nf (Γ , A) B} → lam a ≡ lam b → a ≡ b
lam-inj = {!!}

wk-inj : ∀ {a b : Val Nf Γ A} → wk a ≡ wk b → a ≡ b
wk-inj = {!!}

-- encoding equality

encode : Val V Γ A → Val V Γ A → Type
encode {_} {Γ} {A} (ne _) (ne _) = Val Ne Γ A
encode (ne _) (lam _) = ⊥
encode (ne _) (wk _) = ⊥
encode (ne _) true = ⊥
encode (ne _) false = ⊥

encode (lam _) (ne _) = ⊥
encode (lam _) (wk _) = ⊥
encode (lam {Γ} {A} {B} _) (lam _) = Val Nf (Γ , A) B

encode true (ne x) = ⊥
encode true (wk _) = ⊥
encode true (true {Γ}) = Val Nf Γ Bool
encode true false = ⊥

encode false (ne x) = ⊥
encode false (wk _) = ⊥
encode false true = ⊥
encode false (false {Γ}) = Val Nf Γ Bool

encode (app _ _) (app {Γ} {A} {A'} _ _) = Val Nf Γ A
encode (app _ _) q = ⊥
encode (app _ _) (if x then x₁ else x₂) = ⊥

encode (wk _) b = {!!}

encode q b = {!!}

encode (if _ then _ else _) (app _ _) = ⊥
encode (if _ then  _ else _) q = ⊥
encode (if _ then  _ else _) (if_then_else {Γ} _ _ _) = Val Ne Γ Bool

_≟_ : ∀ (a b : Val V Γ A) → Dec (a ≡ b)

-- normals --------------------------------------------------------------------

_≟_ {V = Nf} (ne a) (ne b) with a ≟ b
... | yes P = yes (λ i → ne (P i))
... | no ¬P = no λ p → ¬P (ne-inj p)
_≟_ {V = Nf} (ne x) (lam _) = no λ p → subst (encode (ne x)) p x
_≟_ {V = Nf} (ne x) (wk _) = no λ p → subst (encode (ne x)) p x
_≟_ {V = Nf} (ne x) true = no λ p → subst (encode (ne x)) p x
_≟_ {V = Nf} (ne x) false = no λ p → subst (encode (ne x)) p x

_≟_ {V = Nf} (lam a) (lam b) with a ≟ b
... | yes P = yes (λ i → lam (P i))
... | no ¬P = no λ p → ¬P (lam-inj p)
_≟_ {V = Nf} (lam a) (ne _) = no λ p → subst (encode (lam a)) p a
_≟_ {V = Nf} (lam a) (wk _) = no λ p → subst (encode (lam a)) p a


_≟_ {V = Nf} true true = yes (λ i → true)
_≟_ {V = Nf} true (ne _) = no λ p → subst (encode true) p true
_≟_ {V = Nf} true (wk _) = no λ p → subst (encode true) p true
_≟_ {V = Nf} true false = no λ p → subst (encode true) p true

_≟_ {V = Nf} false false = yes (λ i → false)
_≟_ {V = Nf} false (ne _) = no λ p → subst (encode false) p false
_≟_ {V = Nf} false (wk _) = no λ p → subst (encode false) p false
_≟_ {V = Nf} false true = no λ p → subst (encode false) p false

-- neutrals -------------------------------------------------------------------

_≟_ {V = Ne} (app {Γ} {A} f a) (app {Γ} {A'} f' a') with A ≟T A'
... | no ¬p0  = no (λ x → ¬p0 {!!})
... | yes p0 = {!!}
_≟_ {V = Ne} (app f a) q = no (λ p → subst (encode (app f a)) p a)
_≟_ {V = Ne} (app f a) (if b then b₁ else b₂) = no (λ p → subst (encode (app f a)) p a)


wk x ≟ wk y with x ≟ y
... | yes P = yes (λ i → wk (P i))
... | no ¬P = no λ p → ¬P (wk-inj p)

wk x ≟ b = no (λ p → subst (encode (wk x)) p x)

_≟_ (q {Γ} {A}) (b) = {!b!}

if c then a else  b ≟ app _ _ = no (λ p → subst (encode (if c then a else b)) p c)
if c then a else  b ≟ q = no (λ p → subst (encode (if c then a else b)) p c)
if c then tr else f ≟ if c' then tr' else f' = {!!}

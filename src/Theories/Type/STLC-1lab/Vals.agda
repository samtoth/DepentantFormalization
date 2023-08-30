module Theories.STLC.Vals where

open import 1Lab.Prelude hiding (⌜_⌝)
open import Cat.Prelude hiding (⌜_⌝)

open import Data.Dec

open import Theories.STLC.Syntax

data ValKind : Type where Ne Nf : ValKind

variable V : ValKind

data Var : Ctx → Ty → Type where
    vz : Var (Γ , A) A
    vs : Var Γ A → Var (Γ , B) A

data Val : ValKind → Ctx → Ty → Type where
  -- Terms in Normal form
  ne   : Val Ne Γ A → Val Nf Γ A
  lam  : Val Nf (Γ , A) B → Val Nf Γ (A ⇒ B)
  true false : Val Nf Γ 𝔹

  -- Neutral terms (terms that are stuck)
  app  : Val Ne Γ (A ⇒ B) → Val Nf Γ A → Val Ne Γ B
  var  : Var Γ A → Val Ne Γ A
  if_then_else : Val Ne Γ 𝔹 → Val Nf Γ A → Val Nf Γ A → Val Ne Γ A



-- Embedding Vals into Terms -----------------------

⌜_⌝ : Val V Γ A → Term Γ A

-- normals

⌜ ne x ⌝ = ⌜ x ⌝
⌜ lam x ⌝ = lam ⌜ x ⌝
⌜ true ⌝ = true
⌜ false ⌝ = false

-- neutrals

⌜ app f x ⌝ = app ⌜ f ⌝ ⌜ x ⌝
⌜ var v ⌝ = aux v
  where aux : Var Γ A → Term Γ A
        aux vz = q
        aux (vs x) = aux x [ p ]

⌜ if cond then a else b ⌝ = if ⌜ cond ⌝ then ⌜ a ⌝ else ⌜ b ⌝


--------------------------------------------------

-- Injectivity of Val constructors

ne-inj : ∀ {a b : Val Ne Γ A} → ne a ≡ ne b → a ≡ b
ne-inj {a = a} P = ap (en a) P
    where en : Val Ne Γ A → Val Nf Γ A → Val Ne Γ A
          en _ (ne x) = x
          en a (lam _) = a
          en a true = a
          en a false = a

lam-inj : ∀ {a b : Val Nf (Γ , A) B} → lam a ≡ lam b → a ≡ b
lam-inj {a = a} P = ap (mal a) P
  where mal : Val Nf (Γ , A) B → Val Nf Γ (A ⇒ B) → Val Nf (Γ , A) B
        mal a (ne _) = a
        mal _ (lam x) = x


var-inj : ∀ {v v' : Var Γ A} → var v ≡ var v' → v ≡ v'
var-inj {v = v} P = ap (rav v) P
  where rav : Var Γ A → Val Ne Γ A → Var Γ A
        rav a (app _ _) = a
        rav _ (var v) = v
        rav a (if _ then _ else _) = a

app-inj : ∀ {f f' : Val Ne Γ (A ⇒ B)} {a  a'} → app f a ≡ app f' a' → (f ≡ f') × (a ≡ a')
app-inj P = {!   !}
  where ppa : Val Ne Γ (A ⇒ B) × Val Nf Γ A → Val Ne Γ B → Val Ne Γ (A ⇒ B) × Val Nf Γ A
        ppa (_ , _) (app f a) = {! f  !} , {!   !}
        ppa (f , a) (var x) = f , a
        ppa (f , a) (if x then x₁ else x₂) = f , a
        
if-then-else-inj : ∀ {c c' : Val Ne Γ 𝔹} {a a' b b' : Val Nf Γ A} → if c then a else b ≡ if c' then a' else b' → (c ≡ c') × (a ≡ a') × (b ≡ b')
if-then-else-inj P = {! !}

-- encoding equality

Code : Val V Γ A → Val V Γ A → Type
Code (ne a) (ne b) = Code a b
Code (ne _) (lam _) = ⊥
Code (ne _) true = ⊥
Code (ne _) false = ⊥

Code (lam _) (ne _) = ⊥
Code (lam b) (lam b') = Code b b'

Code true (ne x) = ⊥
Code true (true) = ⊤
Code true false = ⊥

Code false (ne x) = ⊥
Code false true = ⊥
Code false (false) = ⊤

Code (app {Γ} {A = A} f a) (app {A = A'} f' a') = (Code f f) ×
                                                 (Σ (A ≡ A')
                                                 (λ P → Code a (subst (λ A → Val Nf Γ A) (sym P) a')))
Code (app _ _) (var _) = ⊥
Code (app _ _) (if x then x₁ else x₂) = ⊥

Code (var _) (app _ _) = ⊥
Code (var v) (var v') = v ≡ v'
Code (var _) (if _ then _ else _) = ⊥

Code (if _ then _ else _) (app _ _) = ⊥
Code (if _ then  _ else _) (var _) = ⊥
Code (if c then a else b) (if c' then a' else b') = (Code c c') × (Code a a') × (Code b b')

encode : {v v' : Val V Γ A} → v ≡ v' → Code v v'
encode {v = ne v} {ne v'} P = encode (ne-inj P)
encode {v = ne v} {lam v'} P = subst (Code (ne v)) P (encode {v = v} refl)
encode {v = ne v} {true} P = subst (Code (ne v)) P (encode {v = v} refl)
encode {v = ne v} {false} P = subst (Code (ne v)) P (encode {v = v} refl)

encode {v = lam v} {ne v'} P = subst (Code (lam v)) P (encode {v = v} refl)
encode {v = lam v} {lam v'} P = encode (lam-inj P)

encode {v = true} {ne v'} P = subst (Code true) P tt
encode {v = true} {true} P = tt
encode {v = true} {false} P = subst (Code true) P tt

encode {v = false} {ne v'} P = subst (Code false) P tt
encode {v = false} {true} P = subst (Code false) P tt
encode {v = false} {false} P = tt

encode {v = app {_} {A} f a} {app {_} {A'} f' a'} P with A ≟T A'
... | yes PA = (encode {v = f} refl) , (PA , {!   !})
... | no ¬PA = let 
                  AA' = subst (Code (app f a)) P ((encode {v = f} refl) , refl , {!   !}) .snd .fst 
                  in absurd (¬PA AA')
encode {v = app v v'} {var x} P = subst (Code (var x)) (sym P) refl
encode {v = app v v'} {if c then a else b} P = subst (Code (if c then a else b)) (sym P) 
          ((encode {v = c} refl) , ((encode {v = a} refl) , (encode {v = b} refl)))

encode {v = var x} {app v' v''} P = subst (Code (var x)) P refl
encode {v = var _} {var _} P = var-inj P
encode {v = var x} {if v' then v'' else v'''} P = subst (Code (var x)) P refl

encode {v = if v then v' else v''} {app f a} P = subst (Code (if v then v' else v'')) P 
                                        ((encode {v = v} refl) , ((encode {v = v'} refl) , (encode {v = v''} refl)))
encode {v = if v then v₁ else v₂} {var x} P = {!   !}
encode {v = if c then a else b} {if c' then a' else b'} P = let (vc , va , vb) =  if-then-else-inj P
                                                            in encode vc , (encode va) , encode vb


-- Variables are also decidable

VCode : Var Γ A → Var Γ A → Type
VCode {Γ , A} {A'} with A ≟T A'
... | yes P = {!   !}
... | no ¬P = λ {v v' → {!   !}}

vs-inj : ∀ {v v' : Var Γ A} → vs v ≡ vs v' → v ≡ v'
vs-inj = {!   !}

_≟V_ : ∀ (v v' : Var Γ A) → Dec (v ≡ v')
_≟V_ {Γ} {A} = {!   !} 

_≟_ : ∀ (a b : Val V Γ A) → Dec (a ≡ b)

-- normals --------------------------------------------------------------------

ne a ≟ ne b with a ≟ b
... | yes P = yes (ap ne P)
... | no ¬P = no (λ P → ¬P (ne-inj P))
ne a ≟ lam b = no encode
ne a ≟ true = no encode
ne a ≟ false = no encode

lam a ≟ ne b = no encode
lam a ≟ lam b with a ≟ b
... | yes P = yes (ap lam P)
... | no ¬P = no (λ P → ¬P (lam-inj P))
true ≟ ne b = no encode
true ≟ true = yes refl
true ≟ false = no encode
false ≟ ne b = no encode
false ≟ true = no encode
false ≟ false = yes refl


-- neutrals -------------------------------------------------------------------


app a a₁ ≟ app b b₁ = {!   !}
app a a₁ ≟ var x = no encode
app a a₁ ≟ if b then b₁ else b₂ = no encode

var x ≟ app b b₁ = no encode
var x ≟ var x' with x ≟V x' 
... | yes P = yes (ap var P)
... | no ¬P = no (λ P → ¬P (var-inj P))
var x ≟ if b then b₁ else b₂ = no encode

if a then a₁ else a₂ ≟ app b b₁ = no encode
if a then a₁ else a₂ ≟ var x = no encode
if a then a₁ else a₂ ≟ if b then b₁ else b₂ = {!   !}



val-is-set : ∀ v {Γ A} →  is-set (Val v Γ A)
val-is-set v = Discrete→is-set _≟_  


-- Model -----------------------------------------------------------------------
module Model where
  open import Theories.STLC.Model
  open import Cat.Functor.Base
  open import Cat.CartesianClosed.Instances.PSh
  open import Cat.Morphism using (_≅_)
  open import Cat.Functor.Naturality
  open import Cat.Diagram.Product
  import Cat.Functor.Hom 

  private
    vq : ∀ v {Γ A} → Val v (Γ , A) A
    vq Ne = var vz
    vq Nf = ne (var vz)

    tonf : Val V Γ A → Val Nf Γ A
    tonf {V = Ne} x = ne x
    tonf {V = Nf} x = x
    
    _[_]nf : Val Nf Γ A → Subst (Val Nf) Δ Γ → Val Nf Δ A
    v [ γ ]nf = {! v γ  !}

    𝕋nf : Ty → (PSh lzero (Ctxs (Val Nf))) .Precategory.Ob
    𝕋nf A .Functor.F₀ Γ = el (Val Nf Γ A) (val-is-set Nf)
    𝕋nf A .Functor.F₁ γ v = v [ γ ]nf
    𝕋nf A .Functor.F-id = {!   !}
    𝕋nf A .Functor.F-∘ = {!   !}



  NF : STLC {lzero} {lzero}
  NF .STLC.𝓒 = Ctxs (Val Nf)
  NF .STLC.𝓒-term = Ctxs-terminal (Val Nf)
  NF .STLC.Ty = Ty
  NF .STLC.𝕋 = {!   !}
  NF .STLC.extend = is-model.generic-ctx-extension (Val Nf) (ne (var vz))
  NF .STLC.extension Γ A = to-natural-iso the-iso
    where open Binary-products (PSh lzero (Ctxs (Val Nf))) (PSh-products {κ = lzero} {C = (Ctxs (Val Nf))}) hiding (⟨_,_⟩)
          open Cat.Functor.Hom (Ctxs (Val Nf))
          the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ 𝕋nf A) Hom[-, Γ , A ]
          the-iso .make-natural-iso.eta Γ (γ , a) = ⟨ γ , {!   !} ⟩
          the-iso .make-natural-iso.inv Γ extend = (SComp p extend) , {!   !}
          the-iso .make-natural-iso.eta∘inv = {!   !}
          the-iso .make-natural-iso.inv∘eta = {!   !}
          the-iso .make-natural-iso.natural = {!   !}
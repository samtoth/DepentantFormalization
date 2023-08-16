{-# OPTIONS --cubical #-}
module Foundations.Prelude where

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming (primSubOut to outS)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )


open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )
open import Agda.Builtin.Sigma public

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

subst : ∀ {ℓ ℓ'} {A : Type ℓ} {x y} (P : A → Type ℓ') → Path A x y → P x → P y
subst P eq x = transp (λ i → (P (eq i))) i0 x

data Lift {ℓ} (A : Type ℓ)  (ℓ' : Level) : Type (ℓ-max ℓ ℓ') where
 lift : A → Lift A ℓ'


_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
_∙_ {x = x} p q = λ i → hcomp (λ j → (λ { (i = i0) → x ; (i = i1) → p j  })) (q i)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

cong : (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)
{-# INLINE cong #-}

cong₂ : {C : (a : A) → (b : B a) → Type ℓ} →
        (f : (a : A) → (b : B a) → C a b) →
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        PathP (λ i → C (p i) (q i)) (f x u) (f y v)
cong₂ f p q i = f (p i) (q i)
{-# INLINE cong₂ #-}


refl : ∀ {ℓ} → {A : Type ℓ} → {a : A} → a ≡ a
refl {a = a} i = a

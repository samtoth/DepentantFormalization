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

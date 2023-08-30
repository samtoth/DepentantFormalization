{-# OPTIONS --cubical #-}
module Categories.Category.Free where

open import Foundations.Prelude

open import Categories.Category.Base

data FreeHoms {ℓ ℓ' : Level} (Ob : Type ℓ) (Homs : Ob → Ob → Type ℓ') : Ob → Ob → Type (ℓ-max ℓ ℓ') where
  FreeId   : {x : Ob} → FreeHoms {ℓ} {ℓ'} Ob Homs x x
  FreeComp : {x y z : Ob} → (f : FreeHoms {ℓ} {ℓ'} Ob Homs y z) → (g : FreeHoms {ℓ} {ℓ'} Ob Homs x y) → FreeHoms {ℓ} {ℓ'} Ob Homs x z
  Special  : {x y : Ob} → Homs x y → FreeHoms Ob Homs x y

  -- idL      : {x y : Ob} → (g : FreeHoms {ℓ} {ℓ'} Ob Homs x y) → FreeComp {ℓ} {ℓ'} (FreeId {x = y}) g                ≡ g
  -- idR      : {x y : Ob} → (f : FreeHoms {ℓ} {ℓ'} Ob Homs x y) → FreeComp {ℓ} {ℓ'} f                (FreeId {x = x}) ≡ f

  -- assoc    : {x y : Ob} → (f  )

Free : {ℓ ℓ' : Level} →  (Ob : Type ℓ) → (Ob → Ob → Type ℓ') → Category ℓ (ℓ-max ℓ ℓ')
Free O H = Cat O (FreeHoms O H)


instance
  catFree : ∀ {ℓ ℓ'} {Ob} {Homs} → IsCategory (Free {ℓ} {ℓ'} Ob Homs)
  IsCategory.Id catFree = FreeId
  (catFree IsCategory.∘ f) g = FreeComp f g


open import Categories.Functor
open Category
open IsCategory {{...}}
open Functor

{-# TERMINATING #-}
FunctorFromFree : ∀ {ℓ ℓ'} {O : Type ℓ} {Homs : O → O → Type ℓ'} {ℓc ℓc'} {𝓒 : Category ℓc ℓc'} {{ 𝓒cat : IsCategory 𝓒 }}
                    (fob : O → 𝓒 .Ob)
                    (fhom : ∀ {a b} → Homs a b → 𝓒 .Hom (fob a) (fob b))
                    → Functor (Free O Homs) 𝓒
F0 (FunctorFromFree fo fh) = fo
F1 (FunctorFromFree fo fh) FreeId = Id
F1 (FunctorFromFree fo fh) (FreeComp f g) = FunctorFromFree fo fh .F1 f ∘ FunctorFromFree fo fh .F1 g
F1 (FunctorFromFree fo fh) (Special x) = fh x

{-# OPTIONS --cubical --cumulativity #-}
module Categories.CATS where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Functor
open import Categories.TYPE

private
  variable
    ℓ ℓ' : Level

CATS : Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-suc (ℓ-max ℓ ℓ'))
Category.Ob (CATS {ℓ} {ℓ'}) = Category ℓ ℓ'
Category.Hom CATS = Functor

open Functor {{...}}

module _ {ℓ : Level} {ℓ' : Level} where

  open IsCategory {{...}}

  instance
    CATSisCat : IsCategory (CATS {ℓ} {ℓ'})
    CATSisCat .Id = record { F0 = Id  ; F1 = Id }
    CATSisCat ._∘_ = λ F G → record { F0 = F .F0 ∘ G .F0 ; F1 = F .F1 ∘ G .F1 }

  open import Categories.Diagram.Two

  open Category

  instance
    CATSHasProducts : HasProducts CATS
    HasProducts.hasLimit CATSHasProducts {a} {b} = record {
        lim = record {
                     apex = Cat (a .Ob × b .Ob ) λ ab cd → (a .Hom (π₁ ab) (π₁ cd)) × (b .Hom (π₂ ab) (π₂ cd))
                   ; arrows = λ { 𝟎 → record { F0 = π₁ ; F1 = λ α → {!π₁ α!} } ; 𝟏 → record { F0 = π₂ ; F1 = {!!} }}
                   }
      ; lim-initial = {!!}
      }

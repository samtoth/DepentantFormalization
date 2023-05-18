{-# OPTIONS --cubical --cumulativity #-}
module Categories.Diagram.Base where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Functor
open import Categories.CATS

private
  variable
    ℓ ℓ' : Level

module _ (𝓙 𝓒 : Category ℓ ℓ') where
  Diagram : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  Diagram = CATS [ 𝓙 ,  𝓒 ]


module _ {𝓙 𝓒 : Category ℓ ℓ'} ⦃ ccat : IsCategory 𝓒 ⦄  where
  open Category {{...}}
  open IsCategory ccat
  open Functor {{...}}

  record Cone (D : Diagram 𝓙 𝓒) : Type (ℓ-max ℓ ℓ') where
    field
      apex   : 𝓒 .Ob
      arrows : (x : 𝓙 .Ob) → 𝓒 [ apex , D .F0 x ]


  Cones : (D : Diagram 𝓙 𝓒) → Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-suc (ℓ-max ℓ ℓ'))
  Category.Ob (Cones D) = Cone D
  Category.Hom (Cones D) = λ C1 C2 → 𝓒 [ C1 .apex , C2 .apex ]
    where open Cone

  instance
    ConesCat :  {D : Diagram 𝓙 𝓒} → IsCategory (Cones D)
    IsCategory.Id ConesCat = Id
    IsCategory._∘_ ConesCat = _∘_

  record HasLimit (D : Diagram 𝓙 𝓒) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
    field
      lim          : Cones D .Ob
      lim-initial  : ∀ (x : Cones D .Ob) →  Cones D [ x , lim ]

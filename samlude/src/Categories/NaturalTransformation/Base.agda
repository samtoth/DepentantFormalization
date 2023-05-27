
{-# OPTIONS --cubical --cumulativity #-}
module Categories.NaturalTransformation.Base where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor


open Category {{...}}
open Functor {{...}}

NatTrans : { ℓC ℓC' ℓD ℓD' : Level}
           {C : Category ℓC ℓC'} {D :  Category ℓD ℓD'}
           (F G : Functor C D) → Type (ℓ-suc (ℓ-max ℓC ℓD'))
NatTrans {C = C} {D = D} F G = ∀ (a : C .Ob) → D [ F .F0 a , G .F0 a ]

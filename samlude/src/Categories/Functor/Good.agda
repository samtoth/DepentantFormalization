{-# OPTIONS --cubical #-}
module Categories.Functor.Good where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Functor

open Category
open Functor
open IsCategory {{...}}

record Good {ℓ𝓒 ℓ𝓒' ℓ𝓓 ℓ𝓓'} {𝓒  : Category ℓ𝓒 ℓ𝓒'} {𝓓 : Category ℓ𝓓 ℓ𝓓'} {{𝓒cat : IsCategory 𝓒}} {{𝓓cat : IsCategory 𝓓}}
                   (F : Functor 𝓒 𝓓) : Type (ℓ-max (ℓ-max ℓ𝓒 ℓ𝓒') (ℓ-max ℓ𝓓 ℓ𝓓')) where
  field
    id      : ∀ {a : 𝓒 .Ob} → F .F1 (Id {a = a}) ≡ Id
    distrib : ∀ {a b c} {f : Hom 𝓒 b c}  {g : Hom 𝓒 a b} → F .F1 (f ∘ g) ≡ F .F1 f ∘ F .F1 g

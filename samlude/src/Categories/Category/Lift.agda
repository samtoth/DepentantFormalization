{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Lift where

open import Foundations.Prelude
open import Categories.Category.Base

open import Categories.Functor

Lift : ∀ {ℓ ℓ' ℓ'' ℓ'''} → Category ℓ ℓ' → Category (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')
Lift (Cat o h) = Cat o (λ a b → h a b)

lift : ∀ {ℓ ℓ' ℓ'' ℓ'''} {𝓒 : Category ℓ ℓ'} → Functor 𝓒 (Lift {ℓ} {ℓ'} {ℓ''} {ℓ'''} 𝓒)
Functor.F0 lift = λ x → x
Functor.F1 lift = λ f → f

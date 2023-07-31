{-# OPTIONS --cubical #-}
module Categories.Category.Lift where

open import Foundations.Prelude
open import Categories.Category.Base

open import Categories.Functor

LiftC : ∀ {ℓ ℓ'}  → Category ℓ ℓ' → (ℓ'' ℓ''' : Level) → Category (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')

Category.Ob (LiftC (Cat o h) ℓ ℓ') = Lift o ℓ
Category.Hom (LiftC (Cat o h) ℓ ℓ') (lift x) (lift y) = Lift (h x y) ℓ'

liftC : ∀ {ℓ ℓ' } {𝓒 : Category ℓ ℓ'} → {ℓ'' ℓ''' : Level} → Functor 𝓒 (LiftC 𝓒 ℓ'' ℓ''')
Functor.F0 liftC x = lift x
Functor.F1 liftC f = lift f

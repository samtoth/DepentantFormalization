{-# OPTIONS --cubical --cumulativity #-}
module Data.Bool where

open import Foundations.Prelude

open import Agda.Builtin.Bool public

not : Bool → Bool
not false = true
not true = false

-- A function mapping true to an inhabited type and false to an empty
-- type.

open import Categories.TYPE

open import Categories.Diagram.Zero
open Initial {{...}}
open Terminal {{...}}

T : ∀ {ℓ} → Bool → Type ℓ
T true  = ⊤
T false = ⊥

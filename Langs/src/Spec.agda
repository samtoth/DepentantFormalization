{-#  OPTIONS --cubical --cumulativity #-}
module Spec where

open import Foundations.Prelude
open import Categories.Category
open import Data.Nat renaming (Nat to ℕ)
open import Data.Fin


-- A language spec is a family of types representing the label and the arrity of the term
lang-spec : Type₁
lang-spec = Type → Type

⟦_⟧ : lang-spec → TYPE ↦ TYPE
⟦_⟧ = ?

∅ = Fin 0

𝟙 = Fin 1

𝟚 = Fin 2
𝟛 = Fin 3
𝟜 = Fin 4




data Cosmos : Type ℓ where
  pretype : ℕ → Cosmos
  fibrant : ℕ → Cosmos
  prop    : ℕ → Cosmos
  strict  : ℕ → Cosmos
  omega   : Cosmos

data Pure : lang-spec where
  var : ℕ → Pure ∅
  lam : Pure 𝟙
  pi  : Pure 𝟚
  app : Pure 𝟚


data Total : lang-spec where
  sigma  : Total 𝟚
  pair   : Total 𝟚
  Σelim  : Total 𝟚

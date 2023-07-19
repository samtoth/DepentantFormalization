{-#  OPTIONS --cubical --cumulativity #-}
module Spec where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Category.Bicategory
open import Categories.BICATS
open import Categories.TYPE
open import Categories.Functor

open IsBicategory {{...}}
-- open import Data.Nat renaming (Nat to ℕ)
-- open import Data.Fin


data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

postulate
  Fin : ℕ → Type

{-# BUILTIN NATURAL ℕ #-}

module _ {ℓ} where

  -- A language spec is a family of types representing the label and the arrity of the term
  lang-spec : ∀ {ℓ'} → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  lang-spec  {ℓ'} = Type ℓ' → Type ℓ

  open Ops {E𝓒 = BICATS ℓ ℓ}
  open Functor

  ⟦_⟧ : ∀  {ℓ'} → lang-spec {ℓ'} → ({!!} ↦ {!!})
  -- ⟦ F ⟧ .F0 x = ∀ {arr} (s : F arr) → (arr → x) → x
  -- ⟦ F ⟧ .F1 = ?


  ∅ = Fin 0

  𝟙 = Fin 1

  𝟚 = Fin 2
  𝟛 = Fin 3
  𝟜 = Fin 4

  -- data Cosmos {ℓ} : Type ℓ where
  --   pretype : ℕ → Cosmos
  --   fibrant : ℕ → Cosmos
  --   prop    : ℕ → Cosmos
  --   strict  : ℕ → Cosmos
  --   omega   : Cosmos

  -- data Pure : lang-spec {ℓ} where
  --   var : ℕ → Pure ∅
  --   lam : Pure 𝟙
  --   pi  : Pure 𝟚
  --   app : Pure 𝟚

  -- data Total : lang-spec {ℓ-suc _} where
  --   sigma  : Total 𝟚
  --   pair   : Total 𝟚
  --   Σelim  : Total 𝟚

{-#  OPTIONS --cubical --cumulativity #-}
module Spec where

open import Foundations.Prelude
open import Categories.Category
open import Categories.Category.Bicategory
open import Categories.BICATS
open import Categories.TYPE
open import Categories.Functor

open IsBicategory {{...}}
open import Data.Nat renaming (Nat to ℕ)
open import Data.Fin


module _ {ℓ} {ℓ'} where

  -- A language spec is a family of types representing the label and the arrity of the term
  -- lang-spec : Type (ℓ-suc (ℓ-max ℓ ℓ'))
  lang-spec = Type ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))

  open Ops {E𝓒 = BICATS (ℓ-suc (ℓ-max ℓ (ℓ-suc ℓ'))) (ℓ-suc (ℓ-max ℓ (ℓ-suc ℓ')))} hiding (_∘_)
  open IsCategory {{...}}
  open Functor

  ⟦_⟧ : lang-spec → ∣ TYPE (ℓ-max ℓ (ℓ-suc ℓ')) ∣  ↦ ∣ TYPE (ℓ-max ℓ (ℓ-suc ℓ')) ∣
  ⟦ F ⟧ .F0 x = Σ _ (λ arr → Σ (F arr) (λ _ → (arr → x)))
  ⟦ F ⟧ .F1 f (arr , s , arg) = arr , s , (f ∘ arg)


  ∅ = Fin 0

  𝟙 = Fin 1

  𝟚 = Fin 2
  𝟛 = Fin 3
  𝟜 = Fin 4

  data Cosmos {ℓ} : Type ℓ where
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

  data Total : lang-spec  where
    sigma  : Total 𝟚
    pair   : Total 𝟚
    Σelim  : Total 𝟚



  test : MONAD [ FreeMonad ⟦ Pure ⟧ , Id ]
  test = ?

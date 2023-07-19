{-# OPTIONS --cubical --cumulativity --allow-unsolved-metas #-}
module Data.Nat where

open import Foundations.Prelude

open import Agda.Builtin.Nat public
  using (zero; suc ; _+_) renaming (Nat to ℕ)

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Σ ℕ λ k → k + m ≡ n

open import Foundations.Decidable


_≤?_ : (x y : ℕ) → Dec (x ≤ y)
x ≤? y = {!!}

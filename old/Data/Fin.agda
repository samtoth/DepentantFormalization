{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Data.Fin where

open import Foundations.Prelude
open import Foundations.Decidable

open import Data.Nat

data Fin : ℕ → Type where
  zero : ∀ {n} → Fin n
  suc  : ∀ {n} → Fin n → Fin (suc n)


open import Agda.Builtin.FromNat

open import Data.Bool

#_ : ∀ (m : ℕ) {n : ℕ} { _ : T (isYes (suc m ≤? n)) } → Fin n
(# m) {n} {p} = {!!}

number : ∀ n → Number (Fin n)
number n = record
  { Constraint = λ m → True (suc m ≤? n)
  ; fromNat    = λ m {{pr}} → (# m) {n} {pr}
  }

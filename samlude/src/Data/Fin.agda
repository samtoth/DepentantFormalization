{-# OPTIONS --cubical --cumulativity #-}
module Data.Fin where

open import Foundations.Prelude

open import Data.Nat

data Fin : Nat → Type where
  zero : ∀ {n} → Fin n
  suc  : ∀ {n} → Fin n → Fin (suc n)

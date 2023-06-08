{-# OPTIONS --cubical --cumulativity #-}
module Data.Nat where

open import Foundations.Prelude

data Nat : Type where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

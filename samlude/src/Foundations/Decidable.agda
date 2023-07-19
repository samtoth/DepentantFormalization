{-# OPTIONS --cubical --cumulativity #-}
module Foundations.Decidable where

open import Data.Bool
open import Foundations.Prelude
open import Categories.Negation
open import Categories.TYPE
open import Categories.Category

open IsCategory {{...}}

infix 2 _because_


data Reflects {p} (P : Type p) : Bool → Type p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : Bool
    proof : Reflects P does

open Dec public

pattern yes p = true because ofʸ  p
pattern no ¬p = false because (ofⁿ ¬p)

private
  variable
    p q : Level
    P : Set p
    Q : Set q

isYes : Dec P → Bool
isYes (true  because _) = true
isYes (false because _) = false

isNo : Dec P → Bool
isNo = not ∘ isYes

True : Dec P → Set
True Q = T (isYes Q)

False : Dec P → Set
False Q = T (isNo Q)

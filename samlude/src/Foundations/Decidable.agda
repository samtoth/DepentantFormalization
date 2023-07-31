{-# OPTIONS --cubical #-}
module Foundations.Decidable where

open import Data.Bool
open import Foundations.Prelude
open import Categories.TYPE
open import Categories.Category

open IsCategory {{...}}

infix 2 _because_


module _ {ℓ} where

  open import Categories.Negation {𝓒 = TYPE ℓ}

  data Reflects (P : Type ℓ) : Bool → Type ℓ where
    ofʸ : ( p :   P) → Reflects P true
    ofⁿ : (¬p : ¬ P) → Reflects P false

  record Dec (P : Type ℓ) : Type ℓ where
    constructor _because_
    field
      does  : Bool
      proof : Reflects P does

open Dec public

pattern yes p = true because ofʸ  p
pattern no ¬p = false because (ofⁿ ¬p)


isYes : ∀ {ℓ} {P : Type ℓ} → Dec P → Bool
isYes (true  because _) = true
isYes (false because _) = false

isNo : ∀ {ℓ} {P : Type ℓ} → Dec P → Bool
isNo Q = not (isYes Q) -- not ∘ isYes  - This would be nice - but odly I think i would have to lift the function not to a different level - if only cumulativity played nicer with agda

True : ∀ {ℓ} {P : Type ℓ} → Dec P → Type
True Q = T (isYes Q)

False : ∀ {ℓ} {P : Type ℓ} → Dec P → Type
False Q = T (isNo Q)

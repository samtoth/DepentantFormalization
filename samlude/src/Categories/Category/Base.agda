{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Base where

open import Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

record Category (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    constructor Cat
    field
        Ob : Type ℓ
        Hom : Ob → Ob → Type ℓ'

open Category {{...}}

_[_,_] : (c : Category ℓ ℓ') → (a b : c .Ob) → Type ℓ'
_[_,_] c = c .Hom


record IsCategory (cat : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
        Id : ∀ {a : cat .Ob} → cat .Hom a a
        _∘_ : ∀ {a b c : cat .Ob} → cat .Hom b c → cat .Hom a b → cat .Hom a c

open IsCategory {{...}}

_[_∘_] : (cat : Category ℓ ℓ') ⦃ _ : IsCategory cat ⦄ → {a b c : cat .Ob} → (f : cat [ b , c ]) → (g : cat [ a , b ]) → cat [ a , c ]
cat [ f ∘ g ] = f ∘ g

_^op : Category ℓ ℓ' → Category ℓ ℓ'
Cat Ob Hom ^op = Cat Ob λ a b → Hom b a

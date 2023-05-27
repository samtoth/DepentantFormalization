{-# OPTIONS --cubical --cumulativity #-}
module Categories.Category.Enriched where


open import Foundations.Prelude

record Enriched {ℓ ℓ'} (E : Type ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor ECat
  field
    Ob  : Type ℓ
    Hom : Ob → Ob → E

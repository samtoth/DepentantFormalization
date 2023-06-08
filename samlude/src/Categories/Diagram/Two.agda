{-# OPTIONS --cubical --cumulativity #-}
module Categories.Diagram.Two where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Category.Discrete renaming (Id to Strict)
open import Categories.Functor
open import Categories.Diagram.Base


data 𝟚 {ℓ : Level} : Type ℓ where
  𝟎 𝟏 : 𝟚


2Cat : ∀ {ℓ ℓ'} → Category ℓ (ℓ-max ℓ ℓ')
2Cat {ℓ} {ℓ'} = Discrete {ℓ} {ℓ'} 𝟚


open Functor


ProdDi : ∀ {ℓ ℓ'} {𝓒' : Category ℓ (ℓ-max ℓ ℓ')} ⦃ _ : IsCategory 𝓒' ⦄ (a b :  Category.Ob 𝓒' ) → Diagram (2Cat {ℓ} {ℓ'}) 𝓒'
F0 (ProdDi x _) 𝟎 = x
F0 (ProdDi _ y) 𝟏 = y
F1 (ProdDi {{cc}} x y) {𝟎} (refl {.𝟎}) = Id
  where open IsCategory cc
F1 (ProdDi {{cc}} x y) {𝟏} (refl {.𝟏}) = Id
  where open IsCategory cc

record HasProducts {ℓ ℓ'} (𝓒 : Category ℓ (ℓ-max ℓ ℓ')) ⦃ 𝓒cat : IsCategory 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Limit
  open HasLimit {{...}}

  field
    {{hasLimit}} : ∀ {a b : Category.Ob 𝓒} → HasLimit (ProdDi {ℓ} {ℓ'} { 𝓒' = 𝓒} {{𝓒cat}} a b)


module _ {ℓ ℓ'} {𝓒 : Category ℓ (ℓ-max ℓ ℓ')} ⦃ 𝓒cat : IsCategory 𝓒 ⦄ ⦃ Prods : HasProducts {ℓ} {ℓ'} 𝓒 ⦄ where

  open Category 𝓒
  open IsCategory 𝓒cat
  open Functor
  open Limit
  open Cone
  open HasProducts Prods
  open HasLimit {{...}}

  _×_ : Ob → Ob → Ob
  a × b = lim {D = ProdDi a b} .apex


  π₁ : ∀ {a b} → Hom (a × b) a
  π₁ = lim .arrows 𝟎


  π₂ : ∀ {a b} → Hom (a × b) b
  π₂ = lim .arrows 𝟏


  ×⟨_,_⟩ : {a b P : Ob} → Hom P a → Hom P b → Hom P (a × b)
  ×⟨ f , g ⟩ = lim-initial (record { apex = _ ; arrows = λ { 𝟎 → f ; 𝟏 → g} })

record HasCoproducts {ℓ ℓ'} (𝓒 : Category ℓ ℓ') ⦃ 𝓒cat : IsCategory 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Limit {𝓙 = 2Cat {ℓ} {ℓ'}} {𝓒 = 𝓒 ^op}

  open HasLimit {{...}}

  field
    {{hasColim}} : ∀ {a b : Category.Ob (𝓒 ^op) } → HasLimit (ProdDi {ℓ} {ℓ'} {𝓒' = 𝓒 ^op} {{catOp}} a b)

module _ {ℓ ℓ'} {𝓒 : Category ℓ ℓ'} ⦃ 𝓒cat : IsCategory 𝓒 ⦄ ⦃ Coprods : HasCoproducts 𝓒 ⦄ where
  open Category (𝓒 ^op)
  open IsCategory (catOp ⦃ 𝓒cat ⦄)
  open Functor
  open Limit
  open Cone
  open HasCoproducts Coprods

  _＋_ : Ob → Ob → Ob
  a ＋ b = lim .apex
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

  inj₀ : ∀ {a b } → Hom (a ＋ b) a
  inj₀ {a} {b} = lim .arrows 𝟎
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

  inj₁ : ∀ {a b } → Hom (a ＋ b) b
  inj₁ {a} {b} = lim .arrows 𝟏
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

  ＋⟨_,_⟩ : {a b P : Ob} → Hom P a → Hom P b → Hom P (a ＋ b)
  ＋⟨_,_⟩ {a} {b} f g = lim-initial (record { apex = _ ; arrows = λ { 𝟎 → f ; 𝟏 → g} })
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

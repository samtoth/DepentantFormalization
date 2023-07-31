{-# OPTIONS --cubical #-}
module Categories.Diagram.Two where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Category.Discrete renaming (Id to Strict)
open import Categories.Category.Lift
open import Categories.Functor
open import Categories.Diagram.Base


data 𝟚 : Type where
  𝟎 𝟏 : 𝟚


2Cat : Category (ℓ-zero) (ℓ-zero)
2Cat  = Discrete 𝟚


open Functor


ProdDi : ∀ {ℓ ℓ'} {𝓒' : Category ℓ ℓ'} ⦃ _ : IsCategory 𝓒' ⦄ (a b :  Category.Ob 𝓒' ) → Diagram (LiftC 2Cat ℓ ℓ')  𝓒'
F0 (ProdDi x _) (lift 𝟎) = x
F0 (ProdDi _ y) (lift 𝟏) = y
F1 (ProdDi {𝓒' = _} ⦃ cc ⦄ x y) {lift 𝟎} {lift 𝟎} (lift refl) = Id
  where open IsCategory cc
F1 (ProdDi {𝓒' = _} ⦃ cc ⦄ x y) {lift 𝟏} {lift 𝟏} (lift refl) = Id
  where open IsCategory cc

record HasProducts {ℓ ℓ'} (𝓒 : Category ℓ ℓ') ⦃ 𝓒cat : IsCategory 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Limit
  open HasLimit {{...}}

  field
    {{hasLimit}} : ∀ {a b : Category.Ob 𝓒} → HasLimit (ProdDi {ℓ} { 𝓒' = 𝓒} {{𝓒cat}} a b)


module _ {ℓ ℓ'} {𝓒 : Category ℓ ℓ'} ⦃ 𝓒cat : IsCategory 𝓒 ⦄ ⦃ Prods : HasProducts {ℓ} 𝓒 ⦄ where

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
  π₁ = lim .arrows (lift 𝟎)


  π₂ : ∀ {a b} → Hom (a × b) b
  π₂ = lim .arrows (lift 𝟏)

  ×⟨_,_⟩ : {a b P : Ob} → Hom P a → Hom P b → Hom P (a × b)
  ×⟨ f , g ⟩ = lim-initial (record { apex = _ ; arrows = λ { (lift 𝟎) → f ; (lift 𝟏) → g} })

record HasCoproducts {ℓ ℓ'} (𝓒 : Category ℓ ℓ') ⦃ 𝓒cat : IsCategory 𝓒 ⦄ : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

  open Limit {𝓙 = LiftC 2Cat ℓ (ℓ-max ℓ ℓ') } {𝓒 = 𝓒 ^op}

  open HasLimit {{...}}

  field
    {{hasColim}} : ∀ {a b : Category.Ob (𝓒 ^op) } → HasLimit (ProdDi {ℓ}  {𝓒' = 𝓒 ^op} {{catOp}} a b)

module _ {ℓ} {𝓒 : Category ℓ ℓ} ⦃ 𝓒cat : IsCategory 𝓒 ⦄ ⦃ Coprods : HasCoproducts 𝓒 ⦄ where
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
  inj₀ {a} {b} = lim .arrows (lift 𝟎)
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

  inj₁ : ∀ {a b } → Hom (a ＋ b) b
  inj₁ {a} {b} = lim .arrows (lift 𝟏)
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

  ＋⟨_,_⟩ : {a b P : Ob} → Hom P a → Hom P b → Hom P (a ＋ b)
  ＋⟨_,_⟩ {a} {b} f g = lim-initial (record { apex = _ ; arrows = λ { (lift 𝟎) → f ; (lift 𝟏) → g} })
    where open HasLimit  {D = ProdDi {𝓒' = 𝓒 ^op} {{catOp}} a b} hasColim

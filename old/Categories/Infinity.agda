{-# OPTIONS --cubical --cumulativity --guardedness #-}
module Categories.Infinity where

open import Foundations.Prelude
open import Categories.Category.Enriched


record ∞-category (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) ℓ')
record ∞-functor {ℓ ℓ' : Level} (𝓒 𝓓 : ∞-category ℓ ℓ') : Type (ℓ-max ℓ ℓ')

⊤ : ∀ {ℓ ℓ'} → ∞-category ℓ ℓ'
_×_ : ∀ {ℓ ℓ'} (A B : ∞-category ℓ ℓ') → ∞-category ℓ ℓ'

record ∞-category ℓ ℓ' where
  coinductive
  field
    Ob  : Type ℓ
    Hom : ∀ (A B : Ob) → ∞-category ℓ ℓ'

    Id  : ∀ (A : Ob) → ∞-functor ⊤ (Hom A A)

    _∘_ : ∀ {A B C : Ob} → ∞-functor (Hom B C × Hom A B) (Hom A B)

open ∞-category

record ∞-functor 𝓒 𝓓 where
  coinductive
  field
    F0   : 𝓒 .Ob → 𝓓 .Ob
    Fs : ∀ {A B : 𝓒 .Ob} → ∞-functor (𝓒 .Hom A B) (𝓓 .Hom (F0 A) (F0 B))

open import Categories.Diagram.Zero
open import Categories.TYPE

Idfun : ∀ {ℓ ℓ'} (𝓒 : ∞-category ℓ ℓ') → ∞-functor 𝓒 𝓒
∞-functor.F0 (Idfun 𝓒) = λ x → x
∞-functor.Fs (Idfun 𝓒) = Idfun (𝓒 .Hom _ _)

∞-category.Ob ⊤ = Terminal.⊤ {𝓒 = TYPE _} (record {})
∞-category.Hom ⊤ A B = ⊤
∞-category.Id ⊤ A = Idfun _
∞-category._∘_ ⊤ = {!!}

A × B = {!!}

-- open import Categories.Groupoid
-- open import Categories.Category


{-
record ∞-groupoid {ℓ ℓ'} : Type (ℓ-max (ℓ-suc ℓ) ℓ')
record ∞-Functor {ℓ ℓ'} (𝓖 𝓗 : ∞-groupoid {ℓ} {ℓ'}) : Type (ℓ-max (ℓ-suc ℓ) ℓ')

record ∞-groupoid {ℓ ℓ'} where
  coinductive
  field
    γ   : Enriched ℓ (∞-groupoid {ℓ} {ℓ'})
    _⁻¹ : ∀ {A B} → ∞-Functor (γ .Hom A B) (γ .Hom B A)

open ∞-groupoid

record ∞-Functor {ℓ ℓ'} 𝓖 𝓗 where
  coinductive
  field
    F0 : 𝓖 .γ .Ob → 𝓗 .γ .Ob
    F1 : ∀ {A B} → ∞-Functor (𝓖 .γ .Hom A B) (𝓗 .γ .Hom (F0 A) (F0 B))
-}

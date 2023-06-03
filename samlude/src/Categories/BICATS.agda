{-# OPTIONS --cubical --cumulativity --allow-unsolved-metas #-}
module Categories.BICATS where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Category.Enriched
open import Categories.Category.Bicategory

open import Categories.TYPE
open import Categories.CATS
open import Categories.FUNCTORS
open import Categories.Functor

open import Categories.Diagram.Two

open IsCategory {{...}}
open Functor

BICATS : ∀ {ℓ ℓ'} → Enriched {ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')} (Category (ℓ-max ℓ ℓ') (ℓ-suc (ℓ-max ℓ ℓ')))
Enriched.Ob (BICATS {ℓ} {ℓ'}) = Σ (Category ℓ ℓ') IsCategory
Enriched.Hom BICATS x y = F[ x .fst , y .fst ]

instance
  BICATSBicat : IsBicategory BICATS
  IsBicategory.eIsCat BICATSBicat {y = y} = FCat {{y .snd}}
  IsBicategory.Id BICATSBicat {y} = Id
  F0 (IsBicategory.Comp BICATSBicat) (F , G) = F ∘ G
  F1 (IsBicategory.Comp BICATSBicat {z = z}) {F , G} {F' , G'} (α , β) a = F' .F1 (β a) ∘z α (G .F0 a)
     where open IsCategory (z .snd) renaming (_∘_ to _∘z_)


open Enriched BICATS
open import Categories.Algebra.Monad
module BicatMonad (M : Monad BICATS) where

  open Ops
  open Monad

  open Category (M .x .fst) renaming (Ob to xOb ; Hom to xHom)

  private
    instance
      _ : IsCategory (M .x .fst)
      _ = M .x .snd


  _* : ∀ {a b : xOb } → xHom a (M .F .F0 b) → xHom (M .F .F0 a) (M .F .F0 b)
  _* {a} {b} f = (M .x .fst) [ M .μ b ∘ (M .F .F1 f) ]

  open import Categories.Diagram.Zero

  open Terminal {{...}}


  >>= : ∀ {b : xOb} (a : Functor ⊤ (M .x .fst)) → xHom (xHom ? (M .F .F0 b))  M .F .F0 b
  >>= = ?

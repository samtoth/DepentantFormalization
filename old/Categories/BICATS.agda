{-# OPTIONS --cubical --cumulativity #-}
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

record BICATob (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor ∣_∣
  field
    cat : Category ℓ ℓ'
    {{snd}} : IsCategory cat

open BICATob

BICATS : ∀ (ℓ ℓ' : Level) → Enriched {ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')} (Category (ℓ-max ℓ ℓ') (ℓ-suc (ℓ-max ℓ ℓ')))
Enriched.Ob (BICATS ℓ ℓ') = BICATob ℓ ℓ'
Enriched.Hom (BICATS ℓ ℓ') x y = F[ x .cat , y .cat ]

instance
  BICATSBicat : ∀ {ℓ} {ℓ'} → IsBicategory (BICATS ℓ ℓ')
  IsBicategory.eIsCat BICATSBicat {y = y} = FCat {{y .snd}}
  IsBicategory.Id BICATSBicat {y} = Id
  F0 (IsBicategory.Comp BICATSBicat) (F , G) = F ∘ G
  F1 (IsBicategory.Comp BICATSBicat {z = z}) {F , G} {F' , G'} (α , β) a = F' .F1 (β a) ∘z α (G .F0 a)
     where open IsCategory (z .snd) renaming (_∘_ to _∘z_)

open import Categories.Algebra.Monad
module BicatMonad {ℓ} {ℓ'} {𝓒} {{𝓒cat : IsCategory 𝓒}} (M : Monad (BICATS ℓ ℓ') {∣ 𝓒 ∣}) where

  open Enriched (BICATS ℓ ℓ')

  open Ops
  open Monad

  open Category (𝓒) renaming (Ob to xOb ; Hom to xHom)


  _* : ∀ {a b : xOb } → xHom a (M .F .F0 b) → xHom (M .F .F0 a) (M .F .F0 b)
  _* {a} {b} f = 𝓒 [ M .μ b ∘ (M .F .F1 f) ]

  open import Categories.Diagram.Zero

  open Terminal {{...}}


  _>>=_ : ∀ ⦃ _ : Terminal 𝓒 ⦄ {a b : xOb} → xHom ⊤ (M .F .F0 a) → xHom a (M .F .F0 b) →  xHom ⊤ (M .F .F0 b)
  _>>=_ {b = b} a f = M .μ b x∘ (M .F .F1 f x∘ a)
    where open IsCategory 𝓒cat using () renaming (_∘_ to _x∘_)

module Free {ℓ} {ℓ'} {𝓒 : Enriched.Ob (BICATS ℓ ℓ')} where
  open import Categories.Diagram.Two

  open Enriched (BICATS ℓ ℓ')

  open HasCoproducts {{...}}
  open HasProducts {{...}}

  open Ops renaming (_∘_ to _b∘_)
  open Monad

  open Category (𝓒 .cat) renaming (Ob to xOb ; Hom to xHom)

  data Fix (E : Type → Type) (k : Type)  : Type where
    fix : E (Fix E k) → Fix E k

  {-# NO_POSITIVITY_CHECK #-}
  data Func (E : Type ℓ → Type ℓ) (k : Type ℓ) : Type ℓ where
    return : k → Func E k
    cont   : E (Func E k) → Func E k

  FreeMonad : (E : ∣ TYPE ℓ ∣ ↦ ∣ TYPE ℓ ∣) → Monad  (BICATS (ℓ-suc ℓ) (ℓ-suc ℓ)) {∣ TYPE ℓ ∣}
  Monad.F (FreeMonad E) = theFunctor E
    where
          theFunctor : (∣ TYPE ℓ ∣ ↦ ∣ TYPE ℓ ∣) → (∣ TYPE ℓ ∣ ↦ ∣ TYPE ℓ ∣)
          F0 (theFunctor E) = Func (E .F0)
          F1 (theFunctor E) f (return x) = return (f x)
          F1 (theFunctor E) f (cont x) = cont (E .F1 (theFunctor E .F1 f) {!x!})

          -- cont (E .F1 (theFunctor E .F1 f) x)

  η (FreeMonad E) a = {!!} -- unsym (inj₀ {a = a})
  μ (FreeMonad E) a = {!!} -- unsym ＋⟨ Id ⦃ catOp ⦄  , sym (𝓒 .cat [  unsym inj₁  ∘  E .F1 (FreeMonad E .μ a)  ]) ⟩

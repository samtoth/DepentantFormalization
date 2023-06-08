{-# OPTIONS --cubical --cumulativity #-}
module Categories.FUNCTORS where

open import Foundations.Prelude

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

open Category {{...}}

F[_,_] : ∀ {ℓC ℓC' ℓD ℓD'} → Category ℓC ℓC' → Category ℓD ℓD' → Category (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) (ℓ-suc (ℓ-max ℓC ℓD'))
F[ C , D ] .Ob  = Functor C D
F[ C , D ] .Hom = NatTrans

open IsCategory {{...}}

module _ {ℓC ℓC' ℓD ℓD'} {𝓒 : Category ℓC ℓC'} {𝓓 : Category ℓD ℓD'} ⦃ dcat : IsCategory 𝓓 ⦄ where
  instance
    FCat : IsCategory F[ 𝓒 , 𝓓 ]
    IsCategory.Id FCat = λ a → Id
    IsCategory._∘_ FCat = λ α β → λ a → 𝓓 [ α a ∘ β a ]

  open import Categories.Diagram.Two
  open HasCoproducts {{...}}
  open import Categories.Diagram.Base
  open Limit
  open Functor

  instance
    FCatCoproducts : ⦃ 𝓓coprod : HasCoproducts 𝓓 ⦄ → HasCoproducts F[ 𝓒 , 𝓓 ]
    F0 (Cone.apex (HasLimit.lim (HasCoproducts.hasColim FCatCoproducts {f} {g}))) x = f .F0 x ＋ g .F0 x
    F1 (Cone.apex (HasLimit.lim (HasCoproducts.hasColim FCatCoproducts {F} {G}))) f =
       unsym ＋⟨
             ((𝓓 ^op) [ sym (F .F1 f) ∘ inj₀ ]) ,
             ((𝓓 ^op) [ sym (G .F1 f) ∘ inj₁ ])
             ⟩




    Cone.arrows (HasLimit.lim (HasCoproducts.hasColim FCatCoproducts {F} {G})) 𝟎 = sym (λ a → unsym inj₀)
    Cone.arrows (HasLimit.lim (HasCoproducts.hasColim FCatCoproducts {F} {G})) 𝟏 = sym (λ a → unsym inj₁)

    HasLimit.lim-initial (HasCoproducts.hasColim FCatCoproducts {F} {G}) cone = sym (λ a →  unsym ＋⟨
                                                   sym (unsym (Cone.arrows cone 𝟎) a)
                                                 , sym (unsym (Cone.arrows cone 𝟏) a)
                                                 ⟩)


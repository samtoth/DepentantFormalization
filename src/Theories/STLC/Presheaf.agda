open import Cat.Prelude
open import Cat.Strict

module Theories.STLC.Presheaf {ℓ} (𝓒 : Precategory ℓ ℓ) where

    private module C = Precategory 𝓒
    open Functor
    open _=>_

    open import Theories.STLC.Model
    -- open import Theories.STLC.Ctxs hiding (ℓ)
    -- open import Theories.STLC.Contextual
    
    open import Cat.Instances.StrictCat
    open import Cat.Instances.Product
    open import Cat.Functor.Base
    open import Cat.Functor.Bifunctor
    open import Cat.Functor.Naturality
    open import Cat.CartesianClosed.Instances.PSh
    open import Cat.Diagram.Product
    open Binary-products (PSh ℓ 𝓒) (PSh-products {C = 𝓒})
    open import Cat.Reasoning (PSh ℓ 𝓒)

    -- this is now trivial via CCC
    open import Theories.STLC.CCC
    PSh-model : STLC
    PSh-model = CCC-model (PSh ℓ 𝓒) (PSh-terminal {C = 𝓒}) (PSh-products {C = 𝓒}) PSh-closed
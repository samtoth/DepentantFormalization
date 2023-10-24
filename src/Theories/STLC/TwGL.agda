open import Theories.STLC.Model
open import Cat.Displayed.Base
open Displayed 
module Theories.STLC.TwGL (𝓢 : STLC) (λ𝔹 : STLC-lam-bool .Ob[ 𝓢 ]) where

open STLC 𝓢

open import Cat.Prelude
open import Cat.Functor.Base

module C = Precategory 𝓒

open import Theories.STLC.Vals
open Model
open import Theories.STLC.Presheaf 𝓒
open import Theories.STLC.Ctxs

Ps = PSh lzero (Rens ?)
module PS = Precategory Ps
𝓢ₚ = PSh-model
module Sₚ = STLC (PSh-model)



record TwGL : Type where
    field
      Gl-A  : S.Ty
      Gl-⦅A⦆ : Sₚ.Ty

    field 
      uₜ : PS.Hom (ValPs Ne Gl-A) Gl-⦅A⦆
      qₜ : PS.Hom Gl-⦅A⦆ (ValPs Nf Gl-A)
    
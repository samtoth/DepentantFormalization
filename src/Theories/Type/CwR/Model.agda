module Theories.Type.CwR.Model where

open import Cat.Prelude
open import Cat.Strict
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Diagram.Terminal
open import Theories.Type.CwR
open import Theories.Type.CwR.DFibs
module _ {ℓ} where

    -- A Model of a theory 𝒯 is a Hom from 𝒯 to DFibs in CwRs
    record Model {𝓒 : Precategory (lsuc ℓ) ℓ} (𝒯 : CwR 𝓒) : Type (lsuc (lsuc ℓ)) where
        field M◇          : Precategory ℓ ℓ
        field M-terminal  : Terminal M◇
        field {F}         : Functor 𝓒 (DFibs ℓ M◇)
        field M           : CwR-Hom F 𝒯 (DFibs-cwr ℓ M◇)

        

        
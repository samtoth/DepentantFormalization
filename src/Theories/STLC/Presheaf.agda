open import Cat.Prelude

module Theories.STLC.Presheaf {o} {ℓ} κ (𝓒 : Precategory (o ⊔ lsuc ℓ) ℓ) where

    module C = Precategory 𝓒
    open Functor
    open _=>_

    open import Theories.STLC.Model
    open import Theories.STLC.Ctxs hiding (ℓ)
    open import Theories.STLC.Contextual

    open import Cat.Functor.Base
    open import Cat.CartesianClosed.Instances.PSh

    open Precategory

    Psh-model : Contextual
    Psh-model .Contextual.Typ = PSh κ 𝓒  .Ob
    Psh-model .Contextual.TrmSet = {!   !}
    Psh-model .Contextual._[_]C = {!   !}
    Psh-model .Contextual.Cid = {!   !}
    Psh-model .Contextual.idL = {!   !}
    Psh-model Contextual.[id]C = {!   !}
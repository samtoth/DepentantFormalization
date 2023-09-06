open import Cat.Prelude
open import Cat.Bi.Base
     
module Cat.Bi.Diagram.Pullback {o ℓ ℓ'} (𝓒 : Prebicategory o ℓ ℓ') where

  import Cat.Reasoning as CR
  open import Cat.Functor.Base
  open Prebicategory 𝓒

  private variable
    P′ X Y Z : Ob
    h p₁' p₂' : X ↦ Y
    
  record is-pullback {P} (p₁ : P ↦ X) (f : X ↦ Z) (p₂ : P ↦ Y) (g : Y ↦ Z)
    : Type (ℓ ⊔ ℓ') where

    no-eta-equality
    field
      square : CR._≅_ (Hom P Z) (f ⊗ p₁) (g ⊗ p₂)

  record Pullback {X Y Z} (f : X ↦ Z) (g : Y ↦ Z) : Type (o ⊔ ℓ ⊔ ℓ') where
    no-eta-equality
    field
      {apex} : Ob
      p₁ : apex ↦ X
      p₂ : apex ↦ Y
      has-is-pb : is-pullback p₁ f p₂ g

    open is-pullback has-is-pb public


    
  has-pullbacks : Type _
  has-pullbacks = ∀ {A B X} (f : A ↦ X) (g : B ↦ X) → Pullback f g

  module Pullbacks (all-pullbacks : has-pullbacks) where
    module pullback {x y z} (f : x ↦ z) (g : y ↦ z) =
      Pullback (all-pullbacks f g)

    Pb : ∀ {x y z} → x ↦ z → y ↦ z → Ob
    Pb = pullback.apex

  
{-# OPTIONS --allow-unsolved-metas #-}

open import 1Lab.Prelude renaming (_∘_ to _⊙_)
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Functor.Base
import Cat.Reasoning as CR

module Cat.Bi.Instances.Cats.Complete where

  module _ {o} {ℓ} where
    
    open Prebicategory (Cat o (o ⊔ ℓ))
    open import Cat.Bi.Diagram.Pullback (Cat o (o ⊔ ℓ))
    open Pullback

    Cats-pullback : ∀ {A B X} → (f : A ↦ X) → (g : B ↦ X) → Pullback f g 
    Cats-pullback {A} {B} {X} f g = PB
      where 
            open Functor  
            module A = Precategory A
            module B = Precategory B
            module X = Precategory X

            pbObs : Type _
            pbObs = Σ[ x ∈ A.Ob ] Σ[ y ∈ B.Ob  ] (f .F₀ x ≡ g .F₀ y)

            pbHom : (p q : pbObs) → Type _
            pbHom p q = Σ[ fA ∈ A.Hom (p .fst) (q .fst) ]
                        Σ[ fB ∈ B.Hom (p .snd .fst) (q .snd .fst) ]
                            (PathP (λ i → X.Hom (p .snd .snd i) (q .snd .snd i)) (f .F₁ fA) (g .F₁ fB))


            pbcat : Precategory o (o ⊔ ℓ)
            pbcat .Precategory.Ob = pbObs
            pbcat .Precategory.Hom = pbHom
            pbcat .Precategory.Hom-set = {!   !}
            pbcat .Precategory.id = A.id , (B.id , {!   !})
            pbcat .Precategory._∘_ (fp , gp , p=) (fq , gq , q=) = (fp A.∘ fq) , (gp B.∘ gq) , {!   !} 
            pbcat .Precategory.idr = {!   !}
            pbcat .Precategory.idl = {!   !}
            pbcat .Precategory.assoc = {!   !}

            PB : Pullback f g
            PB .Pullback.apex = pbcat
            PB .Pullback.p₁ = record { F₀ = fst ; F₁ = fst ; F-id = refl ; F-∘ = λ _ _ → refl }
            PB .Pullback.p₂ = record { F₀ = fst ⊙ snd ; F₁ = fst ⊙ snd ; F-id = refl ; F-∘ = λ _ _ → refl }
            PB .Pullback.has-is-pb = {!   !} 
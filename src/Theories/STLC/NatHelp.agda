module Theories.STLC.NatHelp where
    
open import Cat.Prelude
open import Cat.Functor.Base
open Functor
open import Cat.Functor.Naturality
open import Cat.Functor.Compose

_▶_ : ∀ {Ao Aℓ} {A : Precategory Ao Aℓ} {Bo Bℓ} {B : Precategory Bo Bℓ}
            {Co Cℓ} {C : Precategory Co Cℓ} {F G : Functor B C}
            → F => G → (R : Functor A B) → F F∘ R => G F∘ R 
α ▶ R = F∘-functor .F₁ (α , idnt {F = R})

_◀_ : ∀ {Ao Aℓ} {A : Precategory Ao Aℓ} {Bo Bℓ} {B : Precategory Bo Bℓ}
        {Co Cℓ} {C : Precategory Co Cℓ} {F G : Functor A B}
        → (L : Functor B C) → F => G → L F∘ F => L F∘ G 
L ◀ α = F∘-functor .F₁ (idnt {F = L} , α)

α→ : ∀ {Ao Aℓ} {A : Precategory Ao Aℓ} {Bo Bℓ} {B : Precategory Bo Bℓ}
        {Co Cℓ} {C : Precategory Co Cℓ} {Do Dℓ} {D : Precategory Do Dℓ}
        {F : Functor C D} {G : Functor B C} {H : Functor A B}
        → (F F∘ G) F∘ H => F F∘ (G F∘ H)
α→ {D = D} = NT (λ _ → D.id) (λ _ _ _ → D.idl _ ∙ (sym (D.idr _))) where module D = Precategory D

opnt : ∀ {Ao Aℓ} {A : Precategory Ao Aℓ} {Bo Bℓ} {B : Precategory Bo Bℓ} {Co Cℓ} {C : Precategory Co Cℓ}
            {F : Functor B C} {G : Functor A B}
        → Functor.op F F∘ Functor.op G => Functor.op (F F∘ G)
opnt {C = C} = NT (λ _ → C.id) λ _ _ _ → Cop.idl _ ∙ sym (Cop.idr _) 
    where module C = Precategory C
          module Cop = Precategory (C ^op)
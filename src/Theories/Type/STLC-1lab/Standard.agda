module Theories.STLC.Standard where

open import 1Lab.Prelude
open import Cat.Prelude
open import Cat.Morphism hiding (_∘_)
open import Cat.Instances.Sets.Complete
open import Theories.STLC.Model
open import Data.Bool
open import Cat.Diagram.Product
open import Cat.Diagram.Product.Solver
open import Cat.Instances.Functor
open import Cat.Functor.Bifunctor
open import Cat.CartesianClosed.Instances.PSh 
open import Cat.Reasoning (Sets lzero) using (_⟩∘⟨_)
open import Cat.Functor.Hom (Sets lzero)
open Binary-products (Sets lzero) (Sets-products) renaming (⟨_,_⟩ to ×⟨_,_⟩)

StandardModel : STLC
StandardModel .STLC.𝓒 = Sets lzero
StandardModel .STLC.𝓒-term = Sets-terminal
StandardModel .STLC.Ty = Set lzero
-- StandardModel .STLC.ty-set = {!   !}

StandardModel .STLC.𝕋 A = Hom[-, A ] 

StandardModel .STLC.extend A = Right ×-functor A

StandardModel .STLC.extension Γ A  = to-natural-iso the-iso
 where
    open Binary-products (PSh lzero (Sets lzero)) (PSh-products {κ = lzero} {C = Sets lzero}) 
            using () renaming (_⊗₀_ to _⊗₀ᴾ_ )
    the-iso : make-natural-iso (Hom[-, Γ ] ⊗₀ᴾ Hom[-, A ]) Hom[-, A ⊗₀ Γ ]
    the-iso .make-natural-iso.eta _ f x = (f .snd x) , f .fst x
    the-iso .make-natural-iso.inv _ f = (snd ∘ f) , (fst ∘ f)
    the-iso .make-natural-iso.eta∘inv B = funext (λ f →
                                          (λ x → (fst (f x) , snd (f x))) ≡⟨ ⟨⟩∘ {A} {Γ} {el! (Σ[ v ∈ ∣ A ∣ ] ∣ Γ ∣)} {B} {fst} {snd} f  ⟩
                                          (λ x →  fst x , snd x) ∘ f      ≡⟨ ap (_∘ f) (⟨⟩-η {A} {Γ}) ⟩
                                          f                               ∎ 
                                          )
    the-iso .make-natural-iso.inv∘eta B = funext (λ f → refl)
    the-iso .make-natural-iso.natural x y f = refl



StandardModelλ : STLC-lamβη (StandardModel)
StandardModelλ .STLC-lamβη._⇒_ ⟦a⟧ ⟦b⟧ = el! (∣ ⟦a⟧ ∣ → ∣ ⟦b⟧ ∣)

StandardModelλ .STLC-lamβη.lamβη {A} {B} = to-natural-iso the-iso
   where open STLC StandardModel renaming (Hom[-,_] to sHom[-,_])
         the-iso : make-natural-iso (Tm[-⊕ A , B ]) sHom[-, el! (∣ A ∣ → ∣ B ∣) ]
         the-iso .make-natural-iso.eta Γ b ⟦Γ⟧ ⟦a⟧ = b (⟦a⟧ , ⟦Γ⟧)
         the-iso .make-natural-iso.inv Γ f (⟦a⟧ , ⟦Γ⟧) = f ⟦Γ⟧ ⟦a⟧
         the-iso .make-natural-iso.eta∘inv Γ = refl
         the-iso .make-natural-iso.inv∘eta Γ = refl
         the-iso .make-natural-iso.natural x y f = refl


StandardModel𝔹 : STLC-Bool (StandardModel)
StandardModel𝔹 .STLC-Bool.𝔹 = el! Bool
StandardModel𝔹 .STLC-Bool.tru = λ _ → true
StandardModel𝔹 .STLC-Bool.fls = λ _ → false
StandardModel𝔹 .STLC-Bool.elim {A} {Γ} c a b ⟦Γ⟧ with c ⟦Γ⟧
... | true = a ⟦Γ⟧
... | false = b ⟦Γ⟧
StandardModel𝔹 .STLC-Bool.elim-tru = refl
StandardModel𝔹 .STLC-Bool.elim-fls = refl 
{-# OPTIONS --allow-unsolved-metas #-}
module Theories.Type.CwR where

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Functor.Pullback
open import Cat.Functor.Slice
open import Cat.Functor.WideSubcategory
open import Cat.Instances.Slice
open import Cat.Instances.StrictCat
import Cat.Reasoning 
open Functor

module _ {o ℓ} (𝓒 : Precategory o ℓ)
                    (pullbacks : has-pullbacks 𝓒) where

  open Precategory 𝓒

  record Pushforward {A B} (f : Hom A B) : Type (lsuc (o ⊔ ℓ)) where
    field f* : Functor (Slice 𝓒 A) (Slice 𝓒 B)
    field witness : Base-change pullbacks f ⊣ f*

  has-pushforwards = ∀ {A B} (f : Hom A B) → Pushforward f
  
open Pushforward


ForgetSlice : ∀ {o ℓ} {𝓒 : Precategory o ℓ} {A} → Functor (Slice 𝓒 A) 𝓒
ForgetSlice = record { F₀ = /-Obj.domain ; F₁ = /-Hom.map 
                     ; F-id = refl 
                     ; F-∘ = λ f g → refl
                     }

SliceTop : ∀ {o ℓ} {𝓒 : Precategory o ℓ} {t : Terminal 𝓒} → Functor 𝓒 (Slice 𝓒 (Terminal.top t))
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F₀ x ./-Obj.domain = x
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F₀ _ ./-Obj.map = ! where open Terminal t
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F₁ f ./-Hom.map = f
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F₁ f ./-Hom.commutes = sym (!-unique (! ∘ f)) 
    where open Terminal t
          open Precategory 𝓒
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F-id i ./-Hom.map = 𝓒 .Precategory.id
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F-id {x} i ./-Hom.commutes = Hom-set x top (! ∘ id) ! 
                                            (sym (!-unique (! ∘ _)))
                                            (Precategory.id (Slice 𝓒 top) ./-Hom.commutes) i 
    where open Precategory 𝓒
          open Terminal t
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F-∘ {x} {y} {z} f g i ./-Hom.map = f ∘ g where open Precategory 𝓒
SliceTop {𝓒 = 𝓒} {t = t} .Functor.F-∘ {x} {y} {z} f g i ./-Hom.commutes = Hom-set x top
                        (! ∘ f ∘ g) ! 
                        (sym (!-unique (! ∘ f ∘ g)))
                        ((Slice 𝓒 top .Precategory._∘_ 
                            (record { map = f ; commutes = sym (!-unique (! ∘ f)) }) 
                            (record { map = g ; commutes = sym (!-unique (! ∘ g)) })
                          ./-Hom.commutes))
                         i
    where open Precategory 𝓒
          open Terminal t


record CwR {o ℓ} (𝓒 : Precategory o ℓ) : Type (lsuc (o ⊔ ℓ)) where
    field complete : Finitely-complete 𝓒

    open Precategory 𝓒 public
    open Finitely-complete complete public

    field R        : Wide-subcat {C = 𝓒} ℓ
    
    ℛ = Wide R

    module R = Wide-subcat R
    module 𝓡 = Precategory ℛ

    open Terminal terminal public

    field R-stable : is-pullback-stable 𝓒 R.P
    field R-exp    : ∀ {A B} (f : 𝓡.Hom A B) → Pushforward 𝓒 pullbacks (f .Wide-hom.hom)

    -- a General framework Def 3.19 (Polynomial functor associated with f)
    P : ∀ {A B} → (f : 𝓡.Hom A B)  → Functor 𝓒 𝓒
    P f = ForgetSlice F∘  R-exp f .f* F∘ Base-change pullbacks ! F∘ (SliceTop {t = terminal})

record CwR-Hom {o ℓ} {𝓒 𝓓 : Precategory o ℓ} (𝓕 : Functor 𝓒 𝓓) (𝒯 : CwR 𝓒) (ℳ : CwR 𝓓) : Type (lsuc (o ⊔ ℓ)) where
    module 𝒯 = CwR 𝒯
    module ℳ = CwR ℳ
    field lex    : is-lex 𝓕

    field pres-R : ∀ {A B} (f : 𝒯.Hom A B) → 𝒯.R.P f → ℳ.R.P (𝓕 .F₁ f)

    open Wide-hom
    field pres-exp : ∀ {A B} (f : 𝒯.𝓡.Hom A B) 
              → Sliced 𝓕 B F∘ 𝒯.R-exp f .f* 
                  ≅ⁿ
                (ℳ.R-exp (wide (𝓕 .F₁ (f .hom)) (pres-R (f .hom) (f .witness))) .f*) F∘ Sliced 𝓕 A


    𝓕ᴿ : Functor 𝒯.ℛ ℳ.ℛ
    𝓕ᴿ .F₀ = 𝓕 .F₀
    𝓕ᴿ .F₁ f = wide (𝓕 .F₁ (f .hom)) (pres-R (f .hom) (f .witness))
    𝓕ᴿ .F-id i .hom = 𝓕 .F-id i
    𝓕ᴿ .F-id i .witness = is-prop→pathp (λ j → ℳ.R.P-prop (𝓕 .F-id j)) (pres-R 𝒯.id 𝒯.R.P-id) ℳ.R.P-id i
    𝓕ᴿ .F-∘ f g i .hom = 𝓕 .F-∘  (f .hom) (g .hom) i
    𝓕ᴿ .F-∘ f g i .witness = is-prop→pathp (λ j → ℳ.R.P-prop (𝓕 .F-∘ (f .hom) (g .hom) j))
                               (pres-R ((f .hom) 𝒯.∘ (g .hom)) (𝒯.R.P-∘ (f .witness) (g .witness)))
                               (ℳ.R.P-∘ (pres-R (f .hom) (f .witness)) (pres-R (g .hom) (g .witness)))
                               i


CwR-Homs : ∀ {o ℓ} {𝓒 𝓓 : Precategory o ℓ} (𝒯 : CwR 𝓒) (ℳ : CwR 𝓓) → Displayed Cat[ 𝓒 , 𝓓 ] (lsuc (o ⊔ ℓ)) (lsuc (o ⊔ ℓ))
Displayed.Ob[ CwR-Homs 𝒯 ℳ ] = λ F → CwR-Hom F 𝒯 ℳ
Displayed.Hom[ CwR-Homs 𝒯 ℳ ] = λ α F G → Lift _ ⊤
Displayed.Hom[ CwR-Homs 𝒯 ℳ ]-set = λ _ _ _ → hlevel!
CwR-Homs 𝒯 ℳ .Displayed.id′ = _
CwR-Homs 𝒯 ℳ .Displayed._∘′_ = λ _ _ → _
CwR-Homs 𝒯 ℳ .Displayed.idr′ = λ { (lift tt) → refl }
CwR-Homs 𝒯 ℳ .Displayed.idl′ = λ { (lift tt) → refl }
CwR-Homs 𝒯 ℳ .Displayed.assoc′ = λ _ _ _ → refl

-- We can now show that CwR's form a bicategory. If such a thing as Bi-displayed categories existed,
-- then it would be displayed over the bicategory 𝓒𝓐𝓣
-- This is still some amount of work to do - so I will leave out the details of this until such time 
-- as I should need them.

-- instead we can restrict the categories to strict categories (with only sets of objects)
-- and obtain a category displayed over Strict𝓒𝓐𝓣

SCwRs : ∀ {o ℓ} → Displayed (Strict-cats o ℓ) (lsuc (o ⊔ ℓ)) (lsuc (o ⊔ ℓ))
Displayed.Ob[ SCwRs ] (𝓒 , _) = CwR 𝓒
Displayed.Hom[ SCwRs ] 𝓕 𝒯 ℳ = CwR-Hom 𝓕 𝒯 ℳ
Displayed.Hom[ SCwRs ]-set = {!   !}
SCwRs .Displayed.id′ = {!   !}
SCwRs .Displayed._∘′_ = {!   !}
SCwRs .Displayed.idr′ = {!   !}
SCwRs .Displayed.idl′ = {!   !}
SCwRs .Displayed.assoc′ = {!   !}


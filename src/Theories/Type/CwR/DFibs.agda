{-# OPTIONS --allow-unsolved-metas #-}
module Theories.Type.CwR.DFibs where

open import Cat.Prelude
open import Cat.CartesianClosed.Locally
open import Cat.CartesianClosed.Instances.PSh
open import Cat.Diagram.Exponential
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Displayed.Base 
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Cartesian
open import Cat.Functor.WideSubcategory
open import Cat.Instances.StrictCat
open import Cat.Instances.Slice
open import Cat.Strict
open import Cat.Functor.Base
open import Cat.Functor.Adjoint.Continuous
open import Topoi.Base
open import Topoi.Reasoning
open import Theories.Type.CwR
open Functor

-- First, we want to show that any Topos forms a CwR

module _ {o} {𝒯 : Precategory o o} (T : Topos o 𝒯) {prods} {term} where
  
  private module 𝒯 = Precategory 𝒯

  open Cartesian-closed
  open Exponential

  Topos-is-cc : Cartesian-closed 𝒯 prods term
  Topos-is-cc .has-exp A B = exp′ where
    
    open Sheaf-topos T

    module T× = Binary-products 𝒯 prods
    module PSh× = Binary-products (PSh o site) (PSh-products {C = site})

    exp-presheaf : Exponential (PSh o site) _ _ (ι.₀ A) (ι.₀ B)
    exp-presheaf = PSh-closed {C = site} .has-exp (ι.₀ A) (ι.₀ B)

    L-pres-prod : ∀ X Y → 𝒯.Hom (L.₀ X T×.⊗₀ L.₀ Y) (L.₀ (X PSh×.⊗₀ Y))
    L-pres-prod X Y = is-lex.pres-product (Topos.L-lex T) (Terminal.has⊤ (PSh-terminal {C = site}))
                      (PSh-products X Y .Product.has-is-product) .is-product.⟨_,_⟩ T×.π₁ T×.π₂
    

    ι-pres-prod : ∀ X Y → Presh.Hom (ι.₀ X PSh×.⊗₀ ι.₀ Y) (ι.₀ (X T×.⊗₀ Y))
    ι-pres-prod X Y = right-adjoint→is-product (Topos.L⊣ι T) 
                        (prods X Y .Product.has-is-product) .is-product.⟨_,_⟩ PSh×.π₁ PSh×.π₂

    exp′ : Exponential 𝒯 _ _ A B
    exp′ .B^A = L.₀ (exp-presheaf .B^A)
    exp′ .ev = counit.ε _ ∘  L.₁ (exp-presheaf .ev) ∘ L-pres-prod _ _ ∘ (id T×.⊗₁ ε⁻¹.η _)
    exp′ .has-is-exp = is-exp
      where
        open is-exponential
        is-exp : is-exponential 𝒯 prods term _ _
        is-exp .ƛ f = L.₁ (exp-presheaf .has-is-exp .ƛ ((ι.₁ f) Presh.∘ ι-pres-prod _ _))  ∘ ε⁻¹.η _
        is-exp .commutes f = comm where
          comm : (counit.ε _ ∘  L.₁ (exp-presheaf .ev) ∘ L-pres-prod _ _ ∘ (id T×.⊗₁ ε⁻¹.η _)) 
                    ∘ ((L.₁ (exp-presheaf .has-is-exp .ƛ ((ι.₁ f) Presh.∘ ι-pres-prod _ _))  ∘ ε⁻¹.η _) T×.⊗₁ id)
                   ≡ f
          comm = 
            {! _ ∘ (id T×.⊗₁ ε⁻¹.η _) ∘ (_ T×.⊗₁ id  ) ≡⟨ ? ⟩
               _ ∘ (_  T×.⊗₁ id     ) ∘ (id T×.⊗₁ ε⁻.η) ≡⟨ ? ⟩
                                  !}
          {- (counit.ε _ ∘  L.₁ (exp-presheaf .ev) ∘ L-pres-prod _ _ ∘ (id T×.⊗₁ ε⁻¹.η _)) 
                    ∘ ((L.₁ (exp-presheaf .has-is-exp .ƛ ((ι.₁ f) Presh.∘ ι-pres-prod _ _))  ∘ ε⁻¹.η _) T×.⊗₁ id) -}

          --  exp-presheaf .has-is-exp .commutes ((ι.₁ f) Presh.∘ ι-pres-prod _ _)
        is-exp .unique = {!   !}

module _ {o} {𝒯 : Precategory o o} (T : Topos o 𝒯) where

  open Sheaf-topos T
  private module 𝒯 = Precategory 𝒯

  open Locally-cartesian-closed

  Topos-is-lcc : Locally-cartesian-closed 𝒯
  Topos-is-lcc = λ where 
        .has-is-lex → finitely-complete
        .slices-cc x → Topos-is-cc {𝒯 = Slice 𝒯 x} (Slice-topos T x)

  Topos-is-cwr : CwR 𝒯
  Topos-is-cwr .CwR.complete = finitely-complete
  Topos-is-cwr .CwR.R = λ where 
      .Wide-subcat.P _ → Lift _ ⊤
      .Wide-subcat.P-prop _ → hlevel!
      .Wide-subcat.P-id → _
      .Wide-subcat.P-∘ → _
  Topos-is-cwr .CwR.R-stable = _
  Topos-is-cwr .CwR.R-exp f = λ where 
      .Pushforward.f* → lcc→dependent-product 𝒯 Topos-is-lcc (f .hom)
      .Pushforward.witness → lcc→pullback⊣dependent-product 𝒯 Topos-is-lcc (f .hom)


-- In this module we show that the discrete fibrations (DFibs) over
-- some catgory 𝓒 form a Topos and therefor, a CwR.
module _ o (𝓒 : Precategory o o) where

    module 𝓒 = Precategory 𝓒

    
    -- Now we need to establish that DFibs form a category themselves 
    -- Additionally there is a CwR over DFibs via the fact DFibs forms a Topos
    -- And possibly the (intersting but not immediately usefull) equivalence of categories: DFibs ≃ [ 𝓒ᵒᵖ , 𝓢𝓮𝓽 ] 

    open Vertical-fibred-functor
    open Vertical-functor
    open Discrete-fibration

    private unquoteDecl eqvVFF = declare-record-iso eqvVFF (quote Vertical-fibred-functor)
    Fibred-functor-is-set : ∀ ((F , F′) (G , G′) : Σ (Displayed 𝓒 o o) Discrete-fibration) 
                            → is-set (Vertical-fibred-functor F G)
    Fibred-functor-is-set (F , F′) (G , G′) = Iso→is-hlevel 2 eqvVFF (Σ-is-hlevel 2 Vertical-part-is-set is-fibred-is-set)
        where open Discrete-fibration
              module F = Displayed F
              module G = Displayed G

              instance
                Gob : ∀ {x} → H-Level G.Ob[ x ] 2
                Gob {x} = basic-instance 2 (G′ .fibre-set x)

                Ghom : ∀ {k} {a b} {f : 𝓒.Hom a b} {a′ : G.Ob[ a ]} {b′ : G.Ob[ b ]} → H-Level (G.Hom[ f ] a′ b′) (2 + k)
                Ghom {f = f} {a′} {b′} = basic-instance 2 (G.Hom[ f ]-set a′ b′)

                cartesianLevel : ∀ {k} {x y x′ y′} {f : 𝓒.Hom x y} {f′ : G.Hom[ f ] x′ y′} → H-Level (is-cartesian G f f′) (1 + k)
                cartesianLevel = basic-instance 1 (is-cartesian-is-prop G)

              private unquoteDecl eqv = declare-record-iso eqv (quote Vertical-functor)
              Vertical-part-is-set : is-set (Vertical-functor F G)
              Vertical-part-is-set = Iso→is-hlevel 2 eqv (hlevel 2)

              is-fibred-is-set : (α : Vertical-functor F G) → is-set (is-vertical-fibred α)
              is-fibred-is-set α  = hlevel 2
                

    DFibs : Precategory (lsuc o) o
    DFibs .Precategory.Ob = Σ (Displayed 𝓒 o o) Discrete-fibration
    DFibs .Precategory.Hom (F , F′) (G , G′) = Vertical-fibred-functor F G
    DFibs .Precategory.Hom-set F G = Fibred-functor-is-set F G
    DFibs .Precategory.id = IdVf
    DFibs .Precategory._∘_ = _Vf∘_
    DFibs .Precategory.idr _ = Vertical-fibred-functor-path (λ _ → refl) λ _ → refl
    DFibs .Precategory.idl _ = Vertical-fibred-functor-path (λ _ → refl) λ _ → refl
    DFibs .Precategory.assoc f g h = Vertical-fibred-functor-path (λ _ → refl) λ _ → refl

    DFibs-is-strict : (strict : is-strict 𝓒) → is-strict DFibs
    DFibs-is-strict strict = Σ-is-hlevel 2 {! !} {!   !}

    VfF→NT : ∀ {(X , Xf) (Y , Yf) : Σ (Displayed 𝓒 o o)  _} (F : Vertical-fibred-functor X Y) → discrete→presheaf 𝓒 X Xf => discrete→presheaf 𝓒 Y Yf
    VfF→NT {X , Xf} {Y , Yf} F = NT (λ _ → F .F₀′) λ x y f i x′ → Yf .lifts f (F .F₀′ x′) .paths
                                    ((F .vert .F₀′ ((discrete→presheaf 𝓒 X Xf) .F₁ f x′))
                                       , F .F₁′ (transport (Σ-inj-set (Xf .fibre-set x) {!   !}) (Xf .lifts f x′ .centre)))
                                     (~ i) .fst
      where
        lemma : ∀ {x y : 𝓒.Ob} {f : 𝓒.Hom x y} x′ y' f′ → _ ≡ _
        lemma {x} {y} {f} x′ y' f′ = Σ-inj-set (Xf .fibre-set x) (Xf .lifts f x′ .paths (((Xf .lifts f x′ .centre .fst)) , f′))
    
    DFibs→PSh : Functor DFibs (PSh o 𝓒)
    DFibs→PSh .Functor.F₀ (dsp , df) = discrete→presheaf 𝓒 dsp df
    DFibs→PSh .Functor.F₁ {X , Xf} {Y , Yf} F = VfF→NT F
    DFibs→PSh .Functor.F-id = {!   !}
    DFibs→PSh .Functor.F-∘ = {!   !}

    PSh→DFibs : Functor (PSh o 𝓒) DFibs
    PSh→DFibs .F₀ = presheaf→discrete 𝓒
    PSh→DFibs .F₁ = {!   !}
    PSh→DFibs .F-id = {!   !}
    PSh→DFibs .F-∘ = {!   !}

    DFibs-Topos : Topos o DFibs
    DFibs-Topos .Topos.site = 𝓒
    DFibs-Topos .Topos.ι = DFibs→PSh
    DFibs-Topos .Topos.has-ff = {!   !}
    DFibs-Topos .Topos.L = PSh→DFibs
    DFibs-Topos .Topos.L-lex = {!   !}
    DFibs-Topos .Topos.L⊣ι = {!   !}  

    -- DFibs-Terminal : Terminal DFibs
    -- DFibs-Terminal = record { top = the-fib , the-fib-disc ; has⊤ = λ x → contr the-! !-unq }
    --   where
    --     the-fib : Displayed 𝓒 o o
    --     Displayed.Ob[ the-fib ] = λ _ → Lift _ ⊤
    --     Displayed.Hom[ the-fib ] = λ _ _ _ → Lift _ ⊤
    --     Displayed.Hom[ the-fib ]-set = λ _ _ _ → hlevel!
    --     the-fib .Displayed.id′  = _
    --     the-fib .Displayed._∘′_ = _
    --     the-fib .Displayed.idr′ (lift tt) = refl
    --     the-fib .Displayed.idl′ (lift tt) = refl
    --     the-fib .Displayed.assoc′ (lift tt) (lift tt) (lift tt) = refl

    --     the-fib-disc : Discrete-fibration the-fib
    --     the-fib-disc .fibre-set = λ _ → hlevel!
    --     the-fib-disc .lifts = λ f y′ → hlevel!

    --     the-! : ∀ {x} → Vertical-fibred-functor x the-fib
    --     the-! {x} .vert .F₀′ = _
    --     the-! {x} .vert .F₁′ = _
    --     the-! {x} .vert .F-id′ = refl
    --     the-! {x} .vert .F-∘′ = refl
    --     the-! {x} .F-cartesian f′ x₁ .is-cartesian.universal = _
    --     the-! {x} .F-cartesian f′ x₁ .is-cartesian.commutes _ (lift tt) = refl
    --     the-! {x} .F-cartesian f′ x₁ .is-cartesian.unique (lift tt) _ = refl

    --     !-unq : ∀ {x} (f : Vertical-fibred-functor x the-fib) → the-! ≡ f
    --     !-unq f = Vertical-fibred-functor-path (λ x′ i → _) (λ f′ i → _)

    -- DFibs-prod : has-products DFibs
    -- DFibs-prod F G = record { apex = the-fib , fib-disc ; π₁ = pi1 ; π₂ = pi2 
    --                         ; has-is-product = has-prods }
    --   where
    --       module F = Displayed (F .fst)
    --       module Fdf = Discrete-fibration (F .snd)
    --       module G = Displayed (G .fst)
    --       module Gdf = Discrete-fibration (G .snd)
            
    --       the-fib : Displayed 𝓒 o o
    --       Displayed.Ob[ the-fib ] = λ x → F.Ob[ x ] × G.Ob[ x ]
    --       Displayed.Hom[ the-fib ] = λ f A B → F.Hom[ f ] (A .fst) (B .fst) × G.Hom[ f ] (A .snd) (B .snd)
    --       Displayed.Hom[ the-fib ]-set f x y  = ×-is-hlevel 2 
    --                                               (F.Hom[ f ]-set (x .fst) (y .fst)) 
    --                                               (G.Hom[ f ]-set (x .snd) (y .snd))
    --       the-fib .Displayed.id′ = F.id′ , G.id′
    --       the-fib .Displayed._∘′_ (fa , fb) (ga , gb) = (fa F.∘′ ga , fb G.∘′ gb)
    --       the-fib .Displayed.idr′ (ff , fg) i = (F.idr′ ff i) , (G.idr′ fg i)
    --       the-fib .Displayed.idl′ (ff , fg) i = (F.idl′ ff i) , (G.idl′ fg i)
    --       the-fib .Displayed.assoc′ (ff , fg) (gf , gg) (hf , hg) i = (F.assoc′ ff gf hf i) , (G.assoc′ fg gg hg i)
          
    --       fib-disc : Discrete-fibration the-fib
    --       fib-disc .fibre-set x = ×-is-hlevel 2 (Fdf.fibre-set x) (Gdf.fibre-set x)
    --       fib-disc .lifts f (yf , yg) = contr ((Fdf.lifts f yf .centre .fst , Gdf.lifts f yg .centre .fst)
    --                                             , (Fdf.lifts f yf .centre .snd , Gdf.lifts f yg .centre .snd))
    --                                            λ { ((x1 , x2) , (f1 , f2)) i 
    --                                            → (Fdf.lifts f yf .paths (x1 , f1) i .fst , Gdf.lifts f yg .paths (x2 , f2) i .fst)
    --                                              , (Fdf.lifts f yf .paths (x1 , f1) i .snd , Gdf.lifts f yg .paths (x2 , f2) i .snd) }


    --       pi1 : Vertical-fibred-functor the-fib (F .fst)
    --       pi1 .vert = record { F₀′ = fst ; F₁′ = fst ; F-id′ = refl ; F-∘′ = refl }
    --       pi1 .F-cartesian f′ x = {!   !}

    --       pi2 : Vertical-fibred-functor the-fib (G .fst)
    --       pi2 .vert = record { F₀′ = snd ; F₁′ = snd ; F-id′ = refl ; F-∘′ = refl }
    --       pi2 .F-cartesian = {!   !}

    --       has-prods : is-product DFibs pi1 pi2
    --       has-prods .is-product.⟨_,_⟩ f g = record { 
    --                 vert = record { F₀′   = λ o → (f .F₀′ o , g .F₀′ o)
    --                               ; F₁′   = λ x → (f .F₁′ x , g .F₁′ x)
    --                               ; F-id′ = {!   !} 
    --                               ; F-∘′  = {!   !} 
    --                               }
    --               ; F-cartesian = {!   !} 
    --               }
    --       has-prods .is-product.π₁∘factor = Vertical-fibred-functor-path (λ _ → refl) λ _ → refl
    --       has-prods .is-product.π₂∘factor = Vertical-fibred-functor-path (λ _ → refl) (λ _ → refl)
    --       has-prods .is-product.unique h p q = Vertical-fibred-functor-path (λ x′ → {! !}) {!   !}

    -- DFibs-complete : Finitely-complete DFibs
    -- DFibs-complete .Finitely-complete.terminal = DFibs-Terminal
    -- DFibs-complete .Finitely-complete.products = DFibs-prod
    -- DFibs-complete .Finitely-complete.equalisers = {!   !}
    -- DFibs-complete .Finitely-complete.pullbacks = {!   !}

    -- DFibs-exponent : ∀ {A B} (f : DFibs .Precategory.Hom A B) 
    --          → Pushforward DFibs (Finitely-complete.pullbacks DFibs-complete) f
    -- DFibs-exponent f .Pushforward.f* = {!   !}
    -- DFibs-exponent f .Pushforward.witness = {!   !}

    -- DFibs-cwr : CwR DFibs
    -- DFibs-cwr .CwR.complete = DFibs-complete
    -- DFibs-cwr .CwR.R = record { P = λ _ → Lift _ ⊤ ; P-prop = λ _ → hlevel! ; P-id = _ ; P-∘ = _ }
    -- DFibs-cwr .CwR.R-stable = _
    -- DFibs-cwr .CwR.R-exp f = DFibs-exponent (f .hom)

    -- DFibs′ : (strict : is-strict 𝓒) → (∫ SCwRs) .Precategory.Ob
    -- DFibs′ strict = (DFibs , DFibs-is-strict strict) , DFibs-cwr
    
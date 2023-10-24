open import Theories.STLC.Model
open import Theories.STLC.Contextual

module Theories.STLC.Rens {ℓ} (𝓢 : STLC {ℓ}) (SC : Contextual 𝓢) where
    
open import Cat.Prelude

open Functor
open STLC 𝓢 renaming (_⊕_ to _,,_)
open import Data.Dec
open import Cat.Diagram.Terminal

variable
  Γ Δ : Ctx
  A B : Ty

data Els (el : Ty → Type ℓ) : (Γ : Ctx) → Type ℓ where
  ! : Els el ε
  _⊕_ : {Γ : Ctx} {A : Ty} → Els el Γ → el A → Els el (Γ ,, A)

Els-rec : ∀ {ℓ'} {el : Ty → Type ℓ} (P : Type ℓ') → P → (∀ {A} → P → el A → P) → Els el Γ → P
Els-rec P P! Prec ! = P!
Els-rec P P! Prec (els ⊕ x) = Prec (Els-rec P P! Prec els) x

Els-ind : ∀ {ℓ'} {el : Ty → Type ℓ} (P : (Γ : Ctx) → Els el Γ → Type ℓ')
          → (p! : P ε !)
          → (p⊕ : ∀ {Γ} {f} {A} (x : el A) → P Γ f → P (Γ ,, A) (f ⊕ x))
          → ∀ Γ f → P Γ f
Els-ind P p! p⊕ .ε ! = p!
Els-ind P p! p⊕ .(_ ,, _) (f ⊕ x) = p⊕ x (Els-ind P p! p⊕ _ f)

Els-ε-ind : ∀ {ℓ'} {el : Ty → Type ℓ} (P : Els el ε → Type ℓ') → P ! → ∀ f → P f
Els-ε-ind P P! f = {! SC ? !}

Els-,,-ind : ∀ {ℓ'} {el : Ty → Type ℓ} (P : (Γ : Ctx) → Els el Γ → Type ℓ')
             → (p⊕ : ∀ {Γ : Ctx} {f : Els el Γ} {A} → (x : el A) → P Γ f → P (Γ ,, A) (f ⊕ x))
             → ∀ Γ {A} f → P (Γ ,, A) f
Els-,,-ind P p⊕ Γ f = {!  !}

Els-rec₂ : ∀ {ℓ'} {el : Ty → Type ℓ} (P : Type ℓ') → P → (∀ {A} → P → el A → el A → P) → Els el Γ → Els el Γ → P
Els-rec₂ {el = el′} P P! Prec = Els-ind (λ Γ₁ x → Els _ Γ₁ → P) (Els-ε-ind (λ _ → P) P!)
                                  (λ x Pf → Els-,,-ind (λ _ _ → P) (λ _ p → Prec p x {! y  !}) _) _

Els-ind₂ : ∀ {ℓ'} {el : Ty → Type ℓ} (P : {Γ : Ctx} → (A B : Els el Γ) → Type ℓ') 
           → P ! ! → (∀ {Γ} {A} {γ} {δ} {x} {y} → P {Γ} γ δ → P {Γ ,, A} (γ ⊕ x) (δ ⊕ y))
           → ∀ {Γ} γ δ → P {Γ} γ δ
Els-ind₂ P Pε P⊕ {Γ} = Els-ind (λ Δ e' → (e : Els _ Δ) → P e' e) 
                        (Els-ε-ind (λ x → _) Pε)
                         (λ {Γ} x rec e → Els-,,-ind (λ Γ₃ e′ → P (_ ⊕ x) e) (λ ela Past → {! P⊕  !}) Γ e) Γ 

qEls : ∀ {el : Ty → Type ℓ} → Els el (Γ ,, A) → el A
qEls {Γ = Γ} {A = A} {el = ell} = Els-,,-ind (λ Δ _ → ell A) (λ _ x → x) Γ

pEls : ∀ {el : Ty → Type ℓ} → Els el (Γ ,, A) → Els el Γ
pEls = Els-,,-ind (λ Γ x → Els _ _) (λ x x₁ → x₁) _

module hl {el : Ty → Type ℓ} where
  CodeEls : Els el Γ → Els el Γ → Type ℓ
  CodeEls {Γ = Γ} f g = Els-rec₂ (Type ℓ) (Lift _ ⊤) (λ C x y → C × (x ≡ y)) f g

  encode : {xs ys : Els el Γ} → xs ≡ ys → CodeEls xs ys
  encode {xs = xs} {ys} = Els-ind₂ (λ A B → A ≡ B → CodeEls A B) (λ x → {!   !}) {!   !} xs ys
--   encode {xs = ! } { ! } _ = _
--   encode {xs = xs ⊕ x} {ys ⊕ y} P = encode {xs = xs} {ys} (ap pEls P) , ap qEls P

  -- decode : {xs ys : Els el Γ} → CodeEls xs ys → xs ≡ ys
  -- decode {xs = ! } { ! } C = refl
  -- decode {xs = xs ⊕ x} {ys ⊕ y} (C , P) = ap₂ _⊕_ (decode C) P

--   encodeDecode : {xs ys : Els el Γ} → (p : CodeEls xs ys) → encode (decode p) ≡ p
--   encodeDecode {_} { ! } { ! } (lift tt) = refl
--   encodeDecode {_} {xs ⊕ x} {ys ⊕ y} (cp , q) i = encodeDecode cp i , q

--   decodeEncode : {xs ys : Els el Γ} → (p : xs ≡ ys) → decode (encode p) ≡ p
--   decodeEncode = J (λ y p → decode (encode p) ≡ p) de-refl  where
--     de-refl  : {xs′ : Els el Γ} → decode (encode (λ i → xs′)) ≡ (λ i → xs′)
--     de-refl {xs′ = !} = refl
--     de-refl {xs′ = xs ⊕ x} i j = de-refl {xs′ = xs} i j ⊕ x

--   Path≃Code : ∀ {xs ys : Els el Γ} → (xs ≡ ys) ≃ (CodeEls xs ys)
--   Path≃Code = Iso→Equiv (encode , iso decode encodeDecode decodeEncode)

--   Els-hlevel : (n : Nat) → (∀ A → is-hlevel (el A) (2 + n)) → is-hlevel (Els el Γ) (2 + n)
--   Els-hlevel n xhlevel x y = is-hlevel≃ (suc n) Path≃Code Code-is-hlevel where
--     Code-is-hlevel : ∀ {Γ} {x y : Els el Γ} → is-hlevel (CodeEls x y) (suc n)
--     Code-is-hlevel {x = ! } { ! } = hlevel!
--     Code-is-hlevel {x = xs ⊕ x} {ys ⊕ y}  
--       = ×-is-hlevel (suc n) (Code-is-hlevel {x = xs} {ys}) (xhlevel _ x y)

--   instance
--      H-Level-Els : ∀ {n} {k} → ⦃ ∀ {A} → H-Level (el A) (2 + n) ⦄ → H-Level (Els el Γ) (2 + n + k)
--      H-Level-Els {n = n} ⦃ hl ⦄ = 
--       basic-instance (2 + n) (Els-hlevel n (λ A → H-Level.has-hlevel hl))

--   is-set→Els-is-set : (∀ A → is-set (el A)) → is-set (Els el Γ)
--   is-set→Els-is-set ehl = Els-hlevel 0 ehl

-- mapEls : {el₁ el₂ : Ty → Type ℓ} → (∀ {Ty} → el₁ Ty → el₂ Ty) → Els el₁ Γ → Els el₂ Γ
-- mapEls f ! = !
-- mapEls f (s ⊕ x) = mapEls f s ⊕ f x

-- data Var : Ctx → Ty → Type ℓ where
--   vz : ∀ {Γ} {A} → Var (Γ ,, A) A
--   vs : ∀ {Γ} {A} {B} → Var Γ A → Var (Γ ,, B) A
  
-- -- Variables are also decidable


-- VCode : Var Γ A → Var Γ A → Type ℓ
-- VCode {Γ = Γ , B} {B} vz = {!   !}
-- VCode (vs v) vz = Lift _ ⊥
-- VCode (vs v) (vs v') = VCode v v' 

-- module Vhl {Ty-disc : Discrete Ty} where
--   encode : ∀ {Γ} {A : Ty} {v v′ : Var Γ A} → VCode {_} {_} {_} {_} {ℓ} v v′ → v ≡ v′
--   encode {Γ = Γ , A} {B} {v} {v′} Vc with Ty-disc B A | v
--   ... | yes a | v     = let subeq = 
--                               J (λ M a → subst (Var (Γ , A)) a v ≡ subst (Var (Γ , A)) a v′)
--                                {!   !} a
--                         in {!   !}
--   ... | no ¬a | vz    = absurd (¬a refl)
--   ... | no ¬a | vs v₁ = {!   !}

-- vs-inj : ∀ {v v' : Var Γ A} {B} → vs {B = B} v ≡ vs v' → v ≡ v'
-- vs-inj {v = v} = ap (pred v) where
--   pred : Var Γ A → Var (Γ , B) A → Var Γ A
--   pred v vz = v
--   pred _ (vs x) = x


-- Var-Discrete : ∀ {ℓ : Level} (Ty-disc : Discrete Ty) {A : Ty} (v v' : Var Γ A) → Dec (v ≡ v')
-- Var-Discrete  = {!   !} -- Var-ind Motive {!   !} {!   !} where
-- --   Motive : ∀ {Γ} {A} → Var Γ A → Type ℓ
-- --   Motive {Γ = Γ′} {A′} with Ctx-discrete tidy Γ Γ′
-- --   ... | yes a = {!   !}
-- --   ... | no ¬a = {!   !}
-- -- Var-Discrete tidy (vs v) v' = {!   !} 

-- Var-is-set : ∀ (ty-set : is-set Ty) {A : Ty} → is-set (Var Γ A) 
-- Var-is-set = {!   !}

-- Ren : ∀ {ℓ} {Ty : Type ℓ} (A B : Ctx Ty) → Type ℓ
-- Ren Γ Δ = Els (Var Γ) Δ

-- Ren-is-set : ∀ {Γ Δ : Ctx Ty} → is-set Ty → is-set (Ren Γ Δ)
-- Ren-is-set ty-set = hl.is-set→Els-is-set (λ A → Var-is-set ty-set)

-- wk1Ren : Ren Γ Δ → Ren (Γ , A) Δ
-- wk1Ren ! = !
-- wk1Ren (γ ⊕ x) = wk1Ren γ ⊕ vs x

-- wk2Ren : Ren Γ Δ → Ren (Γ , A) (Δ , A)
-- wk2Ren x = (wk1Ren x) ⊕ vz

-- idRen : Ren Γ Γ
-- idRen {Γ = ε} = !
-- idRen {Γ = Γ , x} = wk2Ren idRen

-- _[_]v : Var Γ A → Ren Δ Γ → Var Δ A
-- vz [ _ ⊕ x ]v = x
-- vs v [ γ ⊕ x ]v = v [ γ ]v

-- vsWk1 : ∀ {A B : Ty} (v : Var Γ A) (γ : Ren Δ Γ) → Path (Var (Δ , B) A) (v [ wk1Ren γ ]v) (vs (v [ γ ]v))
-- vsWk1 vz (γ ⊕ x) = refl
-- vsWk1 (vs v) (γ ⊕ x) = vsWk1 v γ

-- _[id]v : (v : Var Γ A) → v [ idRen ]v ≡ v
-- vz [id]v = refl
-- vs v [id]v = vsWk1 v idRen ∙ ap vs (v [id]v)


-- Ren∘ : ∀ {Γ Δ Σ : Ctx Ty} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
-- Ren∘ ! δ = !
-- Ren∘ (γ ⊕ x) δ = (Ren∘ γ δ) ⊕ (x [ δ ]v)

-- _≡[_∘_]v : ∀ {Γ Δ Σ : Ctx Ty} (v : Var Δ A)
--           → (f : Ren Γ Δ) (g : Ren Σ Γ)
--           → v [ Ren∘ f g ]v ≡ (v [ f ]v) [ g ]v
-- vz ≡[ f ⊕ x ∘ g ]v = refl
-- vs v ≡[ f ⊕ x ∘ g ]v = v ≡[ f ∘ g ]v


-- wk1η : ∀ {Γ Δ Σ} {A : Ty} → (γ : Ren Δ Σ) (f : Ren Γ Δ) (x : Var Γ A) → Ren∘ (wk1Ren γ) (f ⊕ x) ≡ Ren∘ γ f 
-- wk1η ! f x = refl
-- wk1η (γ ⊕ _) f x = ap (_⊕ _) (wk1η γ f x)

-- idrRen : ∀ (f : Ren Γ Δ) → Ren∘ f idRen ≡ f
-- idrRen ! = refl
-- idrRen (f ⊕ x) = λ i → (idrRen f i) ⊕ (x [id]v) i

-- idlRen : ∀ (f : Ren Γ Δ) → Ren∘ idRen f ≡ f
-- idlRen ! = refl
-- idlRen (f ⊕ x) = λ i → (wk1η _ _ x ∙ idlRen f) i ⊕ x

-- assocRen : ∀ {Γ Δ Σ Ψ : Ctx Ty} (f : Ren Γ Δ) (g : Ren Σ Γ) (h : Ren Ψ Σ) → Ren∘ f (Ren∘ g h) ≡ Ren∘ (Ren∘ f g) h
-- assocRen ! g h = refl
-- assocRen (f ⊕ x) g h = ap₂ _⊕_ (assocRen f g h) (x ≡[ g ∘ h ]v)

-- Rens : (ty-set : is-set Ty) → Precategory _ _
-- Rens _ .Precategory.Ob = Ctx
-- Rens _ .Precategory.Hom = Ren
-- Rens ty .Precategory.Hom-set _ _ = Ren-is-set ty
-- Rens _ .Precategory.id = idRen
-- Rens _ .Precategory._∘_ = Ren∘
-- Rens _ .Precategory.idr = idrRen
-- Rens _ .Precategory.idl = idlRen
-- Rens _ .Precategory.assoc = assocRen

-- RensTerminal : Terminal (Rens Ty)
-- RensTerminal .Terminal.top = ε
-- RensTerminal .Terminal.has⊤ = λ x → contr ! (λ { ! → refl})

-- wk1∘ : ∀ {Γ Δ Σ} (A : Ty) {B : Ty} (γ : Ren Δ Σ) (δ : Ren Γ Δ) → wk1Ren {A = B} (Ren∘ γ δ) ≡ Ren∘ (wk1Ren γ) (wk2Ren δ)
-- wk1∘ _ ! δ = refl
-- wk1∘ A (γ ⊕ x) δ = ap₂ _⊕_ (wk1∘ A γ δ) (sym (vsWk1 x δ))

-- wk2∘ : ∀ {Γ Δ Σ} (A : Ty) {B : Ty} (γ : Ren Δ Σ) (δ : Ren Γ Δ) → wk2Ren {A = B} (Ren∘ γ δ) ≡ Ren∘ (wk2Ren γ) (wk2Ren δ)
-- wk2∘ _ ! δ = refl
-- wk2∘ A (γ ⊕ x) δ = ap (_⊕ vz) (ap₂ _⊕_ (wk1∘ A γ δ) (sym (vsWk1 x δ)))

-- extendRens : {ty : is-set Ty} → Ty → Functor (Rens ty) (Rens ty)
-- extendRens A .F₀ Γ = Γ , A
-- extendRens A .F₁ = wk2Ren
-- extendRens A .F-id = refl
-- extendRens A .F-∘ f g = wk2∘ A f g

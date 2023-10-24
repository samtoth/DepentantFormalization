{-# OPTIONS --allow-unsolved-metas #-}
open import Theories.STLC.Model
open import Cat.Displayed.Base
open Displayed 
module Theories.STLC.Vals (𝓢 : STLC) (λ𝔹 : Ob[_] STLC-lam-bool 𝓢 ) where

open import 1Lab.Prelude hiding (⌜_⌝)
open import Cat.Prelude hiding (⌜_⌝)
open import Theories.STLC.Ctxs using () renaming (Ctx to CtxV)
open import Data.Dec


data ValKind : Type where Ne Nf : ValKind
  
open STLC 𝓢

variable 
  V : ValKind
  Γ Δ : Ctx
  A B : Ty


module Sl = STLC-lamβη (λ𝔹 .fst)
open Sl using (_⇒_)
module Sb = STLC-Bool (λ𝔹 .snd)
open Sb using (𝔹)

data Var : Ctx → Ty → Type where
  vz : Var (Γ ⊕ A) A
  vs : Var Γ A → Var (Γ ⊕ B) A

data Val : ValKind → Ctx → Ty → Type where
  -- Terms in Normal form
  ne   : Val Ne Γ A → Val Nf Γ A
  lam  : Val Nf (Γ ⊕ A) B → Val Nf Γ (A ⇒ B)
  true false : Val Nf Γ 𝔹

  -- Neutral terms (terms that are stuck)
  app  : Val Ne Γ (A ⇒ B) → Val Nf Γ A → Val Ne Γ B
  var  : Var Γ A → Val Ne Γ A
  if_then_else : Val Ne Γ 𝔹 → Val Nf Γ A → Val Nf Γ A → Val Ne Γ A



-- -- Embedding Vals into Terms -----------------------
-- open import Theories.STLC.HIITctx using (ιSTLC) renaming (Tm to ιTm ; _[_] to _[_]ι)
-- module ι = Theories.STLC.HIITctx

-- ⌜_⌝ : ∀ {Γ'} → Val V (embedCtx Γ') A → ιSTLC ιTm (Γ , A)

-- -- normals

-- ⌜ ne x ⌝ = ⌜ x ⌝
-- ⌜ lam x ⌝ = lam ⌜ x ⌝
-- ⌜ true ⌝ = true
-- ⌜ false ⌝ = false

-- -- neutrals

-- ⌜ app f x ⌝ = app ⌜ f ⌝ [ ⟨ ιSTLC.Id , ⌜ x ⌝ ⟩ ]ι
-- ⌜ var v ⌝ = aux v
--   where aux : Var Γ A → ιSTLC Tm (Γ , A)
--         aux vz = q ιSTLC.Id
--         aux (vs x) = aux x [ p ιSTLC.Id ]

-- ⌜ if cond then a else b ⌝ = ι.elim𝔹 ⌜ cond ⌝ ⌜ a ⌝ ⌜ b ⌝


--------------------------------------------------

-- Injectivity of Val constructors

ne-inj : ∀ {a b : Val Ne Γ A} → ne a ≡ ne b → a ≡ b
ne-inj {a = a} P = ap (en a) P
    where en : Val Ne Γ A → Val Nf Γ A → Val Ne Γ A
          en _ (ne x) = x
          en a (lam _) = a
          en a true = a
          en a false = a

lam-inj : ∀ {a b : Val Nf (Γ ⊕ A) B} → lam a ≡ lam b → a ≡ b
lam-inj {a = a} P = ap (mal a) P
  where mal : Val Nf (Γ ⊕ A) B → Val Nf Γ (A ⇒ B) → Val Nf (Γ ⊕ A) B
        mal a = ?


var-inj : ∀ {v v' : Var Γ A} → var v ≡ var v' → v ≡ v'
var-inj {v = v} P = ap (rav v) P
  where rav : Var Γ A → Val Ne Γ A → Var Γ A
        rav a (app _ _) = a
        rav _ (var v) = v
        rav a (if _ then _ else _) = a

app-inj : ∀ {f f' : Val Ne Γ (A ⇒ B)} {a  a'} → app f a ≡ app f' a' → (f ≡ f') × (a ≡ a')
app-inj P = {!   !}
  where ppa : Val Ne Γ (A ⇒ B) × Val Nf Γ A → Val Ne Γ B → Val Ne Γ (A ⇒ B) × Val Nf Γ A
        ppa (_ , _) (app f a) = {! f  !} , {!   !}
        ppa (f , a) (var x) = f , a
        ppa (f , a) (if x then x₁ else x₂) = f , a
        
if-then-else-inj : ∀ {c c' : Val Ne Γ 𝔹} {a a' b b' : Val Nf Γ A} → if c then a else b ≡ if c' then a' else b' → (c ≡ c') × (a ≡ a') × (b ≡ b')
if-then-else-inj P = {! !}

-- encoding equality

-- Code : Val V Γ A → Val V Γ A → Type
-- Code (ne a) (ne b) = Code a b
-- Code (ne _) (lam _) = ⊥
-- Code (ne _) true = ⊥
-- Code (ne _) false = ⊥

-- Code (lam _) (ne _) = ⊥
-- Code (lam b) b' = Code b ?

-- Code true (ne x) = ⊥
-- Code true (true) = ⊤
-- Code true false = ⊥

-- Code false (ne x) = ⊥
-- Code false true = ⊥
-- Code false (false) = ⊤

-- Code (app {Γ} {A = A} f a) (app {A = A'} f' a') = (Code f f) ×
--                                                  (Σ (A ≡ A')
--                                                  (λ P → Code a (subst (λ A → Val Nf Γ A) (sym P) a')))
-- Code (app _ _) (var _) = ⊥
-- Code (app _ _) (if x then x₁ else x₂) = ⊥

-- Code (var _) (app _ _) = ⊥
-- Code (var v) (var v') = v ≡ v'
-- Code (var _) (if _ then _ else _) = ⊥

-- Code (if _ then _ else _) (app _ _) = ⊥
-- Code (if _ then  _ else _) (var _) = ⊥
-- Code (if c then a else b) (if c' then a' else b') = (Code c c') × (Code a a') × (Code b b')

-- encode : {v v' : Val V Γ A} → v ≡ v' → Code v v'
-- encode {v = ne v} {ne v'} P = encode (ne-inj P)
-- encode {v = ne v} {lam v'} P = subst (Code (ne v)) P (encode {v = v} refl)
-- encode {v = ne v} {true} P = subst (Code (ne v)) P (encode {v = v} refl)
-- encode {v = ne v} {false} P = subst (Code (ne v)) P (encode {v = v} refl)

-- encode {v = lam v} {ne v'} P = subst (Code (lam v)) P (encode {v = v} refl)
-- encode {v = lam v} {lam v'} P = encode (lam-inj P)

-- encode {v = true} {ne v'} P = subst (Code true) P tt
-- encode {v = true} {true} P = tt
-- encode {v = true} {false} P = subst (Code true) P tt

-- encode {v = false} {ne v'} P = subst (Code false) P tt
-- encode {v = false} {true} P = subst (Code false) P tt
-- encode {v = false} {false} P = tt

-- encode {v = app {_} {A} f a} {app {_} {A'} f' a'} P = ?
-- -- with A ≟T A'
-- -- ... | yes PA = (encode {v = f} refl) , (PA , {!   !})
-- -- ... | no ¬PA = let 
-- --                   AA' = subst (Code (app f a)) P ((encode {v = f} refl) , refl , {!   !}) .snd .fst 
-- --                   in absurd (¬PA AA')
-- encode {v = app v v'} {var x} P = subst (Code (var x)) (sym P) refl
-- encode {v = app v v'} {if c then a else b} P = subst (Code (if c then a else b)) (sym P) 
--           ((encode {v = c} refl) , ((encode {v = a} refl) , (encode {v = b} refl)))

-- encode {v = var x} {app v' v''} P = subst (Code (var x)) P refl
-- encode {v = var _} {var _} P = var-inj P
-- encode {v = var x} {if v' then v'' else v'''} P = subst (Code (var x)) P refl

-- encode {v = if v then v' else v''} {app f a} P = subst (Code (if v then v' else v'')) P 
--                                         ((encode {v = v} refl) , ((encode {v = v'} refl) , (encode {v = v''} refl)))
-- encode {v = if v then v₁ else v₂} {var x} P = {!   !}
-- encode {v = if c then a else b} {if c' then a' else b'} P = let (vc , va , vb) =  if-then-else-inj P
--                                                             in encode vc , (encode va) , encode vb


-- _≟_ : ∀ (a b : Val V Γ A) → Dec (a ≡ b)

-- -- normals --------------------------------------------------------------------

-- ne a ≟ ne b with a ≟ b
-- ... | yes P = yes (ap ne P)
-- ... | no ¬P = no (λ P → ¬P (ne-inj P))
-- ne a ≟ lam b = no encode
-- ne a ≟ true = no encode
-- ne a ≟ false = no encode

-- lam a ≟ ne b = no encode
-- lam a ≟ lam b with a ≟ b
-- ... | yes P = yes (ap lam P)
-- ... | no ¬P = no (λ P → ¬P (lam-inj P))
-- true ≟ ne b = no encode
-- true ≟ true = yes refl
-- true ≟ false = no encode
-- false ≟ ne b = no encode
-- false ≟ true = no encode
-- false ≟ false = yes refl


-- -- neutrals -------------------------------------------------------------------


-- app a a₁ ≟ app b b₁ = {!   !}
-- app a a₁ ≟ var x = no encode
-- app a a₁ ≟ if b then b₁ else b₂ = no encode

-- var x ≟ app b b₁ = no encode
-- var x ≟ var x' = ?
-- --  with Var-Discrete {!   !} x x' 
-- -- ... | yes P = yes (ap var P)
-- -- ... | no ¬P = no (λ P → ¬P (var-inj P))
-- var x ≟ if b then b₁ else b₂ = no encode

-- if a then a₁ else a₂ ≟ app b b₁ = no encode
-- if a then a₁ else a₂ ≟ var x = no encode
-- if a then a₁ else a₂ ≟ if b then b₁ else b₂ = {!   !}



val-is-set : ∀ v {Γ A} →  is-set (Val v Γ A)
val-is-set v = ?


-- Model -----------------------------------------------------------------------
module NormModel (Ty-is-set : is-set Ty) where
  open import Theories.STLC.Ctxs using (Rens;Ren;wk2Ren;wk2∘;_[_]v;_[id]v;Ren∘;_≡[_∘_]v)
  open import Cat.Functor.Base
  open import Cat.CartesianClosed.Instances.PSh
  open import Cat.Morphism using (_≅_)
  open import Cat.Functor.Naturality
  open import Cat.Diagram.Product
  import Cat.Functor.Hom 
  open import Cat.Diagram.Terminal
  open Functor
  private
    vq : ∀ v {Γ A} → Val v (Γ ⊕ A) A
    vq Ne = var vz
    vq Nf = ne (var vz)

    tonf : Val V Γ A → Val Nf Γ A
    tonf {V = Ne} x = ne x
    tonf {V = Nf} x = x
    
    toV :  Val Ne Γ A  → Val V Γ A
    toV {V = Ne} = λ x → x
    toV {V = Nf} = ne

  module R = Precategory (Rens (el Ty Ty-is-set) ^op)

  _[_]vRen : Val V Γ A →  Ren Δ Γ → Val V Δ A
  ne v [ γ ]vRen = ne (v [ γ ]vRen)
  lam v [ γ ]vRen = lam (v [ wk2Ren γ ]vRen)
  true [ γ ]vRen = true
  false [ γ ]vRen = false
  app v v' [ γ ]vRen = app (v [ γ ]vRen) (v' [ γ ]vRen)
  var x [ γ ]vRen = var (x [ γ ]v)
  if v then t else f [ γ ]vRen = if v [ γ ]vRen then t [ γ ]vRen else (f [ γ ]vRen)

  _[Id]vRen : ∀ (a : Val V Γ A) → (a [ R.id ]vRen) ≡ a
  ne a [Id]vRen = ap ne (a [Id]vRen)
  lam a [Id]vRen = ap lam (a [Id]vRen)
  true [Id]vRen = refl
  false [Id]vRen = refl
  app a a₁ [Id]vRen = ap₂ app (a [Id]vRen) (a₁ [Id]vRen)
  var x [Id]vRen = ap var (x [id]v)
  if a then t else f [Id]vRen = λ i → if (a [Id]vRen) i then (t [Id]vRen) i else ((f [Id]vRen) i)

  _[_∘_]=vRen : ∀ {Γ Δ Σ : Ctx Ty} (v : Val V Γ A) (f : Ren Δ Γ) (g : Ren Σ Δ) → (v [ Ren∘ f g ]vRen) ≡ (v [ f ]vRen) [ g ]vRen
  ne v [ f ∘ g ]=vRen = ap ne (v [ f ∘ g ]=vRen)
  _[_∘_]=vRen {A = A} (lam v) f g  = λ i → lam (
                                    ( ap (v [_]vRen) (wk2∘ A f g)
                                        ∙
                                      (v [ wk2Ren f ∘ wk2Ren g ]=vRen)) i)
  true [ f ∘ g ]=vRen = refl
  false [ f ∘ g ]=vRen = refl
  app v v₁ [ f ∘ g ]=vRen = ap₂ app (v [ f ∘ g ]=vRen) (v₁ [ f ∘ g ]=vRen)
  var x [ f ∘ g ]=vRen = ap var (x ≡[ f ∘ g ]v)
  if v then v₁ else v₂ [ f ∘ g ]=vRen = λ i → if ((v [ f ∘ g ]=vRen) i) 
                                                then (v₁ [ f ∘ g ]=vRen) i
                                                else ((v₂ [ f ∘ g ]=vRen) i)


  
  ValPs : ValKind → Ty → Functor (Rens (el Ty Ty-is-set) ^op) (Sets lzero)
  ValPs v A .F₀ Γ = el (Val v Γ A) (val-is-set v)
  ValPs v A .F₁ ρ x = x [ ρ ]vRen
  ValPs v A .F-id = funext _[Id]vRen
  ValPs v A .F-∘ f g = funext _[ g ∘ f ]=vRen

  -- -- module SNf = SubstCat (Val Nf)

  -- wk1Sub : Subst (Val V) Γ Δ → Subst (Val V) (Γ , A) Δ
  -- wk1Sub ! = !
  -- wk1Sub (γ ⊕ x) = (wk1Sub γ) ⊕ (x [ wk1Ren idRen ]vRen) 

  -- wk2Sub : Subst (Val V) Γ Δ → Subst (Val V) (Γ , A) (Δ , A)
  -- wk2Sub x = wk1Sub x ⊕ toV (var vz)


  -- {-# TERMINATING #-}
  -- _[_]vSub : Val V Γ A →  Subst (Val Nf) Δ Γ → Val Nf Δ A
  -- ne v [ γ ]vSub = v [ γ ]vSub
  -- lam v [ γ ]vSub = lam (v [ wk2Sub γ ]vSub)
  -- true [ γ ]vSub = true
  -- false [ γ ]vSub = false
  -- app f a [ γ ]vSub with f [ γ ]vSub 
  -- ... | ne f = ne (app f (a [ γ ]vSub))
  -- ... | lam f = f [ (Ren→Subst (Val Nf) (ne ∘ var) idRen) ⊕ (a [ γ ]vSub) ]vSub
  -- var vz [ _ ⊕ x ]vSub = x
  -- var (vs x) [ γ ⊕ _ ]vSub = (var x) [ γ ]vSub
  -- if cond then v1 else v2 [ γ ]vSub with cond [ γ ]vSub
  -- ... | ne c = ne (if c then (v1 [ γ ]vSub) else (v2 [ γ ]vSub))
  -- ... | true = v1 [ γ ]vSub
  -- ... | false = v2 [ γ ]vSub

  -- -- NFS∘ : ∀ {Γ Δ Σ} → SNf.Subst Δ Σ → SNf.Subst Γ Δ → SNf.Subst Γ Σ
  -- -- NFS∘ ! δ = !
  -- -- NFS∘ (γ ⊕ x) δ = (NFS∘ γ δ) ⊕ (x [ δ ]vSub)

  -- -- NFSubs : Precategory lzero lzero
  -- -- NFSubs .Precategory.Ob = Ctx Ty
  -- -- NFSubs .Precategory.Hom = SNf.Subst
  -- -- NFSubs .Precategory.Hom-set = {!   !}
  -- -- NFSubs .Precategory.id = SNf.Ren→Subst (ne ∘ var) idRen
  -- -- NFSubs .Precategory._∘_ = NFS∘ 
  -- -- NFSubs .Precategory.idr = {!   !}
  -- -- NFSubs .Precategory.idl = {!   !}
  -- -- NFSubs .Precategory.assoc = {!   !}

  -- -- Rens→Subs : Functor (Rens Ty) NFSubs
  -- -- Rens→Subs = record { F₀ = id ; F₁ = SNf.Ren→Subst (ne ∘ var) ; F-id = refl ; F-∘ = λ _ _ → {!   !} }

  -- -- _[Rens→Subs] : ∀ {Γ Δ A} (t : Val Nf Γ A) {ρ : Ren Δ Γ} → t [ Rens→Subs .F₁ ρ ]vSub ≡ t [ ρ ]vRen
  -- -- (ne t [Rens→Subs]) {ρ} = {!   !}
  -- -- (lam t [Rens→Subs]) {ρ} = λ i → lam ((t [Rens→Subs]) {{! wk2Ren ρ  !}} i)
  -- -- true [Rens→Subs] = {!   !}
  -- -- false [Rens→Subs] = {!   !}

  -- -- extendSubs : Ty → Functor NFSubs NFSubs
  -- -- extendSubs A .Functor.F₀ = _, A
  -- -- extendSubs A .Functor.F₁ = wk2Sub
  -- -- extendSubs A .Functor.F-id = {!   !}
  -- -- extendSubs A .Functor.F-∘ = {!   !}

  -- -- NFSubsTerm : Terminal NFSubs
  -- -- NFSubsTerm = record { top = ε ; has⊤ = λ x → contr ! (λ { ! → refl }) }

  -- -- Vsub-∘ : ∀ {V} {Γ Δ Σ A} (f : SNf.Subst Σ Δ) (g : SNf.Subst Δ Γ ) (t : Val V Γ A)
  -- --        → Path (Val Nf Σ A) (t [ ((NFSubs ^op) .Precategory._∘_ f g) ]vSub) ((t [ g ]vSub) [ f ]vSub)
  -- -- Vsub-∘ = {!   !}

  -- -- 𝕋nf : Ty → (PSh lzero NFSubs) .Precategory.Ob
  -- -- 𝕋nf A .Functor.F₀ Γ = el (Val Nf Γ A) (val-is-set Nf)
  -- -- 𝕋nf A .Functor.F₁ γ v = v [ γ ]vSub
  -- -- 𝕋nf A .Functor.F-id = funext λ t → (t [Rens→Subs]) ∙ (t [Id]vRen)
  -- -- 𝕋nf A .Functor.F-∘ f g = funext (Vsub-∘ f g)

  -- open import Theories.STLC.Contextual

  -- CNF : Contextual
  -- CNF .Contextual.Typ = Ty
  -- CNF .Contextual.TrmSet Γ A = el (Val Nf Γ A) (val-is-set Nf)
  -- CNF .Contextual._[_]C = _[_]vSub
  -- CNF .Contextual.Cid = Ren→Subst (Val Nf) (ne ∘ var) idRen
  -- CNF .Contextual.idL = {!  !}
  -- CNF .Contextual._[id]C = {!   !}

  -- NF : STLC
  -- NF = ContextualModel CNF

  -- NFBool : STLC-Bool NF
  -- NFBool .STLC-Bool.𝔹 = 𝔹
  -- NFBool .STLC-Bool.tru = true 
  -- NFBool .STLC-Bool.fls = false
  -- NFBool .STLC-Bool.elim (ne x) a b = ne (if x then a else b)
  -- NFBool .STLC-Bool.elim true a _ = a
  -- NFBool .STLC-Bool.elim false _ b = b
  -- NFBool .STLC-Bool.elim-tru = refl
  -- NFBool .STLC-Bool.elim-fls = refl

  -- {-# TERMINATING #-}
  -- NFLam : STLC-lamβη NF
  -- NFLam .STLC-lamβη._⇒_ = _⇒_
  -- NFLam .STLC-lamβη.lamβη = to-natural-iso the-iso
  --   where open STLC NF 
          
  --         the-iso : make-natural-iso (Tm[-⊕_,_] A B) (𝕋 (A ⇒ B))
  --         the-iso .make-natural-iso.eta Γ = lam  
  --         the-iso .make-natural-iso.inv Γ (ne f) = ne (app (f [ wk1Ren idRen ]vRen) (ne (var vz)))
  --         the-iso .make-natural-iso.inv Γ (lam f) = f
  --         the-iso .make-natural-iso.eta∘inv Γ = funext λ {(ne f) → {!   !}
  --                                                       ; (lam f) → refl}
  --         the-iso .make-natural-iso.inv∘eta Γ = refl 
  --         the-iso .make-natural-iso.natural = {!   !} 
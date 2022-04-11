module Try2 where

  open import Data.Nat hiding (_/_)
  open import Data.Fin using (Fin; toℕ)
  open import Data.Bool using (true; false)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  
  open import Relation.Nullary using (Dec; yes; no) 
  open import Relation.Nullary.Decidable using (True; toWitness)

  infixr 7 _⇒_
  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_
  infix 6 _/_

  data Context : Set
  data Type : Context → Set
  data _⊢_ : (Γ : Context) → Type Γ → Set
  data _∋_ : (Γ : Context) → Type Γ → Set
  data _⇒_ : Context → Context → Set
  data _=-ctx_ : Context → Context → Set
  data _=-⋆_ : {Γ Δ : Context} → Type Γ → Type Δ → Set
  data _=-∋_ : {Γ Δ : Context} {τ₁ : Type Γ} { τ₂ : Type Δ} → Γ ∋ τ₁ → Δ ∋ τ₂ → Set
  data _=-⇒_ : {Γ₁ Γ₂ Δ₁ Δ₂ : Context} → (ρ₁ : Γ₁ ⇒ Δ₁) → (ρ₂ : Γ₂ ⇒ Δ₂) →  Set
  data _=-⊢_ : {Γ Δ : Context} {τ₁ : Type Γ} {τ₂ : Type Δ} → Γ ⊢ τ₁ → Δ ⊢ τ₂ → Set

  _/_ : {Γ Δ : Context} → Type Γ → Γ ⇒ Δ → Type Δ

  variable
    Γ : Context
    Δ : Context
    τ : Type Γ

  data Context where
    ∅ : Context
    _,_ : (Γ : Context) → Type Γ → Context

  data Type where
    ⋆ : 
          ----------------------------------------
                      Type Γ
    Π :
          (τ₁ : Type Γ) → (τ₂ : Type (Γ , τ₁))
        → ----------------------------------------
                      Type Γ
    El :
             (t : Γ ⊢ ⋆)
        → ----------------------------------------
                  Type Γ

  _↦_ : (t : Type Γ) → (t₁ : Type (Γ , t)) → Type Γ
  _↦_ = Π

  data _⇒_ where
    sub : Γ ⊢ τ → (Γ , τ) ⇒ Γ
    weaken : (σ : Type Γ) → Γ ⇒ (Γ , σ)
    _↑_ : (ρ : Γ ⇒ Δ) → (σ : Type Γ) → (Γ , σ) ⇒ (Δ , σ / ρ)
    id : Γ ⇒ Γ
    ∘ :{Γ Δ Χ : Context}  → Γ ⇒ Δ → Δ ⇒ Χ → Γ ⇒ Χ 

  data _⊢_ where
     var :
               Γ ∋ τ
         → ---------------------------------------    
               Γ ⊢ τ
     ƛ :
             {τ₁ : Type Γ} → {τ₂ : Type (Γ , τ₁)}
         → ---------------------------------------
                   (t : Γ  ,  τ₁ ⊢ τ₂)
         → ---------------------------------------
                        Γ  ⊢  Π τ₁ τ₂

     _∙_ :
          {τ₁ : Type Γ} → {τ₂ : Type (Γ , τ₁)}
          → --------------------------------------
            (func : Γ ⊢ Π τ₁ τ₂) → (arg : Γ ⊢ τ₁)
          → --------------------------------------
                          Γ ⊢ (τ₂ / sub arg)

     _▷⊢_ :      {τ₁ τ₂ : Type Γ}
          → --------------------------------------
               Γ ⊢ τ₁ → τ₁ =-⋆ τ₂
          → --------------------------------------
                     Γ ⊢ τ₂
     
     _//_ :
                     {τ : Type Γ}
         → --------------------------------
               Γ ⊢ τ   →   (ρ : Γ ⇒ Δ)
         → --------------------------------
                      Δ ⊢ (τ / ρ)

-- _/_ : {Γ Δ : Context} → Type Γ → Γ ⇒ Δ → Type Δ
  ⋆ / ρ = ⋆
  (Π ty ty₁) / ρ = Π (ty / ρ) (ty₁ / (ρ ↑ ty))
  El t / ρ = El (t // ρ)


  data _∋_ where
    vz : {σ : Type Γ} → Γ , σ ∋ (σ / weaken σ)
    vs : Γ ∋ τ → {σ : Type Γ} → Γ , σ ∋ (τ / weaken σ)
    _▷∋_ :  {τ₁ τ₂ : Type Γ} → Γ ∋ τ₁ → τ₁ =-⋆ τ₂ → Γ ∋ τ₂ 

  data _=-ctx_ where
    ∅-cong : ∅ =-ctx ∅ 
    ,-cong : {σ₁ : Type Γ} {σ₂ : Type Δ} → Γ =-ctx Δ → σ₁ =-⋆ σ₂ → (Γ , σ₁) =-ctx (Δ , σ₂)

  data _=-⋆_ where
    ⋆-cong : Γ =-ctx Δ → ⋆ {Γ} =-⋆ ⋆ {Δ}
    Π-cong : {τ₁₁ : Type Γ} {τ₁₂ : Type Δ} {τ₂₁ : Type (Γ , τ₁₁)} {τ₂₂ : Type (Δ , τ₁₂)} → τ₁₁ =-⋆ τ₁₂ → τ₂₁ =-⋆ τ₂₂ → Π τ₁₁ τ₂₁ =-⋆ Π τ₁₂ τ₂₂
    El-cong : {t₁ : Γ ⊢ ⋆} {t₂ : Δ ⊢ ⋆} → t₁ =-⊢ t₂ → El t₁ =-⋆ El t₂ 

  data _=-⇒_ where
    extEq :  ∀{Γ₁ Γ₂ Δ₁ Δ₂ : Context} →  (ρ₁ : Γ₁ ⇒ Δ₁) → (ρ₂ : Γ₂ ⇒ Δ₂) → {σ₁ : Type Γ₁} → {σ₂ : Type Γ₂}
           → Γ₁ =-ctx Γ₂ → Δ₁ =-ctx Δ₂
           → (∀ (v₁ : Γ₁ ∋ σ₁) (v₂ : Γ₂ ∋ σ₂) → v₁ =-∋ v₂ → (var v₁ // ρ₁) =-⊢ (var v₂ // ρ₂)) 
           → ρ₁ =-⇒ ρ₂


  data _=-∋_ where
    vz-cong : {σΓ : Type Γ} {σΔ : Type Δ}
                  → σΓ =-⋆ σΔ
                  → vz {Γ} {σΓ} =-∋ vz {Δ} {σΔ}
                  
    vs-cong : {σΓ : Type Γ} {σΔ : Type Δ} {vΓ : Γ ∋ σΓ} {vΔ : Δ ∋ σΔ}
                  → vΓ =-∋ vΔ
                  → σΓ =-⋆ σΔ
                  → vs vΓ {σΓ} =-∋ vs vΔ {σΔ}
                  
    cast-eq-l : {σΓ : Type Γ} {σΔ : Type Δ} {σΓ₂ : Type Γ} {vΓ : Γ ∋ σΓ} {vΔ : Δ ∋ σΔ} {eq : σΓ =-⋆ σΓ₂}
                  → vΓ =-∋ vΔ
                  → (vΓ ▷∋ eq) =-∋ vΔ 

    cast-eq-r : {σΓ : Type Γ} {σΔ : Type Δ} {σΔ₂ : Type Δ} {vΓ : Γ ∋ σΓ} {vΔ : Δ ∋ σΔ} {eq : σΔ =-⋆ σΔ₂}
                  → vΓ =-∋ vΔ
                  → vΓ =-∋ (vΔ ▷∋ eq) 

  variable
    τ₁ : Type Γ
    τ₂ : Type Δ
    τ₃ : Type Γ
    τ₄ : Type Δ
    t₁ : Γ ⊢ τ₁
    t₂ : Δ ⊢ τ₂
    t₃ : Γ ⊢ τ₃
    t₄ : Δ ⊢ τ₄


  {-# NO_POSITIVITY_CHECK #-}
  data _=-⊢_ where
    refl-⊢ : (t : Γ ⊢ τ) → t =-⊢ t
    sym-⊢ : t₂ =-⊢ t₁ → t₁ =-⊢ t₂
    trans-⊢ : t₁ =-⊢ t₂ → t₂ =-⊢ t₃ → t₁ =-⊢ t₃

    var-cong : {τΓ : Type Γ} {τΔ : Type Δ} {v₁ : Γ ∋ τΓ} {v₂ : Δ ∋ τΔ} → v₁ =-∋ v₂ → var v₁ =-⊢ var v₂ 
    ƛ-cong : t₁ =-⊢ t₂ → ƛ t₁ =-⊢ ƛ t₂
    ∙-cong : {σ₁ : Type (Γ , τ₁)} {f₁ : Γ ⊢ Π τ₁ σ₁}
             {σ₂ : Type (Δ , τ₂)} {f₂ : Δ ⊢ Π τ₂ σ₂}
             → f₁ =-⊢ f₂ → t₁ =-⊢ t₂ → (f₁ ∙ t₁) =-⊢ (f₂ ∙ t₂) 
    //-cong :{ Χ : Context} {ρ₁ : Γ ⇒ Χ} {ρ₂ : Δ ⇒ Χ} →  t₁ =-⊢ t₂ →  ρ₁ =-⇒ ρ₂ → (t₁ // ρ₁) =-⊢ (t₂ // ρ₂)

    cast-eq : {eq : τ₁ =-⋆ τ₃} → (t₁ ▷⊢ eq) =-⊢ t₁

    β : {τ : Type Γ} {σ : Type (Γ , τ)} {t : Γ , τ ⊢ σ} {arg : Γ ⊢ τ} → ((ƛ t) ∙ arg) =-⊢ (t // sub arg)
    η : {τ : Type Γ} {σ : Type (Γ , τ)} {t : Γ ⊢ Π τ σ} → ƛ ((t // weaken τ) ∙ (var vz)) =-⊢ t

    substLam : (ρ : Γ ⇒ Δ) → ((ƛ t₁) // ρ) =-⊢ ƛ (t₁ // (ρ ↑ τ₁))
    substApp : {σ : Type (Γ , τ₁)} {func : Γ ⊢ Π τ₁ σ} {arg : Γ ⊢ τ₁}
               → (ρ : Γ ⇒ Δ)
               → ((func ∙ arg) // ρ) =-⊢ ((func // ρ) ∙ (arg // ρ))
               
    id-vanish : (t₁ // id) =-⊢ t₁
    substComp : {Χ : Context} {ρ₁ : Γ ⇒ Δ} {ρ₂ : Δ ⇒ Χ} → (t₁ // (∘ {Γ} {Δ} {Χ} ρ₁ ρ₂)) =-⊢ ((t₁ // ρ₁) // ρ₂) 
    substWk : (v : Γ ∋ τ₁) → (var v // weaken τ₁) =-⊢ var (vs v {τ₁})
    substVzSub : (var vz // sub t₁) =-⊢ t₁  
    substVsSub : {v : Γ ∋ τ₁} → (var (vs v) // sub t₁) =-⊢ (var v)
    substVzLift : {ρ : Γ ⇒ Δ} → (var vz //  (ρ ↑ τ₁)) =-⊢ var {Γ , ⋆} (vz)
    substVsLift : {ρ : Γ ⇒ Δ} {v : Γ ∋ τ} → (var (vs v) // (ρ ↑ τ₁)) =-⊢ ((var v // ρ) // (weaken (τ₁ / ρ)))
  
  length : Context → ℕ 
  length ∅ = zero
  length (n , x) = suc (length n)

  lookup : (Γ : Context) → (n : ℕ) → n < length Γ → Type Γ  
  lookup (Γ , x) zero p = x / weaken x
  lookup (Γ , x) (suc n) (s≤s p) = lookup Γ n p / weaken x
          
  #_ : {Γ : Context} (n : ℕ) → {p< : n < length Γ} → Γ ⊢ lookup Γ n p<
  #_ {x , x₁} zero = var (vz)
  #_ {x , x₁} (suc c) {s≤s p} = (# c) // weaken x₁
    
  idΠ : Γ ⊢ Π ⋆ (El (var vz) ↦ El (var (vs vz)))
  idΠ {Γ} = ƛ (ƛ ((#_ {Γ , ⋆ , El (var vz)} 0 {s≤s z≤n}) ▷⊢ El-cong (helper {Γ} ⋆ (El (var vz)))))
      where
        helper : {Γ' : Context} (σ₁ : Type Γ') → (σ₂ : Type (Γ' , σ₁)) → (var vz // weaken σ₂) =-⊢ var (vs (vz))
        helper σ₁ σ₂ = {!!} substVzSub


  mutual
    data Atom : Γ ⊢ τ₁ → Set where

    data NF : Γ ⊢ τ₁ → Set where
    

  _ : ∀ (A : Set) → A → A
  _ = λ A x → x

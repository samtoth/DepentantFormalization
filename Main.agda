module Main where

  open import Data.Nat
  open import Data.Fin using (Fin; toℕ)
  open import Data.Bool using (true; false)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  
  open import Relation.Nullary using (Dec; yes; no) 
  open import Relation.Nullary.Decidable using (True; toWitness)

  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_

  infixr 7 _⇒_
  infix  5 ƛ_
  infixl 7 _∙_
  infix  9 #_
  infix 8 ∀⦅_⦆_

  data Term : Set
  data Sort : Term → Set

  data Term where
    _∙_  : Term → Term → Term
    #_   : ℕ → Term
    ƛ⇒_ : Term → Term
    ⋆    : Term
    ∀⦅_⦆_ : Term → (ty : Term) → {t : Sort ty} → Term 

  
  data Value : Term → Set where
    V-ƛ : ∀ {N : Term}
          → Value (ƛ⇒ N)
    V-⋆ : Value ⋆
    V-∀ : ∀ {ty term : Term}
          → {St : Sort term}
          → Value (∀⦅_⦆_ ty term {St})

  postulate
    cong-Sort : ∀ (f : Term → Term) → (x : Term) → {Sort x} → Sort (f x)

  {-# TERMINATING #-}
  _[_≔_] : Term → ℕ → Term → Term
  (x ∙ x₁) [ n ≔ V ] = x [ n ≔ V ] ∙ x₁ [ n ≔ V ]
  (# x) [ n ≔ V ] with x ≟ n
  ... | yes _ = V 
  ... | no _ = # x
  (ƛ⇒ x) [ n ≔ V ] = ƛ⇒ (x [ suc n ≔ V ])
  ⋆ [ n ≔ v ] = ⋆
  (∀⦅_⦆_ x x₁ {sx₁}) [ n ≔ V ] = ∀⦅_⦆_ (x [ n ≔ V ]) (x₁ [ n ≔ V ]) {cong-Sort (λ P → P [ n ≔ V  ]) x₁ {sx₁}} 

      


  infix 4 _⟶_

  data _⟶_ : Term → Term → Set where
    ε¹ : ∀ {L L' M : Term }
       → L ⟶ L'
       → L ∙ M ⟶ L' ∙ M

    ε² : ∀ { V M M' : Term}
       → Value V
       → M ⟶ M'
       → V ∙ M ⟶ V ∙ M'

    β : ∀ { N V : Term }
      → Value V
      → (ƛ⇒ N) ∙ V ⟶ N [ 0 ≔ V ]

  infixr 2 _⟶⟨_⟩_
  infix  3 _∎

  data _->>_ : Term → Term → Set where
    _∎ : (M : Term) → M ->> M

    _⟶⟨_⟩_ : ∀ (L : Term) {M N : Term}
            → L ⟶ M
            → M ->> N
            → L ->> N


  _ : (ƛ⇒ (# 0)) ∙ (ƛ⇒ (# 0)) ⟶ (ƛ⇒ (# zero))
  _ = β V-ƛ

  _ : ((ƛ⇒ (# 0)) ∙ (ƛ⇒ ( # 0)) ∙ (ƛ⇒ ( # 0))) ->> ((ƛ⇒ ( # 0 )))
  _ = ((ƛ⇒ (# 0)) ∙ (ƛ⇒ ( # 0)) ∙ (ƛ⇒ ( # 0)))
      ⟶⟨ ε¹ (β V-ƛ) ⟩
        ((ƛ⇒ ( # 0)) ∙ (ƛ⇒ ( # 0)))
      ⟶⟨ β V-ƛ ⟩
        ((ƛ⇒ ( # 0 )))
      ∎
      
  

  data Context : Set where
    ∅ : Context 
    _,_ : Context → Term → Context


  data _∋_ :  Context → Term → Set where
    Z : {Γ : Context } {A : Term } → Γ , A ∋ A
    S : {Γ : Context } {A : Term } {B : Term } → Γ ∋ A → Γ , B ∋ A

  data _⊢_ : Context → Term → Set where
   `_ : {Γ : Context } {A : Term}
        → Γ ∋ A
        → Γ ⊢ A

   _∙_ : {Γ : Context} {A B : Term} → {Sb : Sort B}
       → Γ ⊢ ∀⦅_⦆_ A B {Sb}
       → Γ ⊢ A
       → Γ ⊢ B 

   ƛ_ : {Γ : Context} {A B : Term} {Sb : Sort B}
      → Γ , A ⊢ B
      → Γ ⊢ ∀⦅_⦆_ A B {Sb}

   `⋆ : {Γ : Context}
      → Γ ⊢ ⋆

   `∀⦅_⦆_ : {Γ : Context} {A B C : Term}
           → Sort A
           → Γ , A , B ⊢ C 
           → Γ ⊢ ⋆

  _⇒_ : Term → (B : Term) → {Sb : Sort B}  → Term
  _⇒_ a b {Sb} = ∀⦅_⦆_ a b {Sb}

  length : Context → ℕ
  length ∅ = zero
  length (x , _) = suc (length x)

  lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Term
  lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
  lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

  count : ∀ {Γ : Context} {n : ℕ}
          → (p : n < length Γ)
          → Γ ∋ lookup p
  count {Γ , x} {zero} (s≤s z≤n) = Z
  count {Γ , x} {suc n} (s≤s x₁) = S (count x₁)

  `#_ : ∀ {Γ : Context}
       → (n : ℕ)
       → {n∈Γ : True (suc n ≤? length Γ)}
       → Γ ⊢ lookup (toWitness n∈Γ)
  `#_ n {n∈Γ} = ` count (toWitness n∈Γ) 

  data Sort where
    Ty-⋆ : Sort ⋆

    Ty-∀ : ∀ {L M : Term}
           → (sm : Sort M)
           → Sort (∀⦅_⦆_ L M {sm})

    Ty-# : {n : ℕ} → {Γ : Context} → (p : n < length Γ) → Sort (lookup p) → Sort (# n)


  _ : Term
  _ = ƛ⇒(ƛ⇒(ƛ⇒(# 1 ∙ (# 1 ∙ # 2))))

  open import Agda.Builtin.Sigma using (Σ)
    renaming (_,_ to _,,_) 

  idT : Σ Term Sort
  idT = (∀⦅_⦆_ ⋆ (∀⦅_⦆_ (# 0) (# 2) {Ty-# {!!} {!!}}) {{!!}} ,, {!!})

  _ : ∀ {Γ : Context} → Γ ⊢ ∀⦅_⦆_ ⋆ (∀⦅_⦆_ (# 0) (# 2) {Ty-# (s≤s (s≤s (s≤s z≤n))) Ty-⋆}) {Ty-∀ (Ty-# (s≤s (s≤s (s≤s z≤n))) Ty-⋆)}
  _ = ƛ (ƛ {!'# 1!})
  
  num : Set → Set
  num A = (A → A) → A → A

  one : ∀ {A : Set} → num A
  one f x = f x

  two : ∀ {A : Set} → num A
  two f x = f (f x)
  

--  Γ ⊢ λX.T : ΠX : κ.κ0 --> Γ, X : κ |- T : κ0 Γ |- κ : *, or even when k = *, by * : * 

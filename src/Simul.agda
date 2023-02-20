module Simul where
open import Calculus
open import Trans
open import Data.Bool renaming (T to Tr)
open import Function
open import Data.Bool 
open import Data.Product hiding (_,_)

private variable
    t t′ t₁ t₂ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-lock : {T (lock?ᵇ Γ)}
             → (t  : Γ ⊢ A) 
             → (t′ : Γ ⊢ A)
             ------------------
             → Γ ⊢ t ~ t′ ∶ A

    sim-var : {F (lock?ᵇ Γ₂)} 
            → {x : A ∈ (Γ₁ ∷ Γ₂)}
            ---------------------------------
            → Γ₁ ∷ Γ₂ ⊢ var x ~ var x ∶ A

    sim-app : Γ ⊢ t₁      ~ t₁′       ∶ A ⇒ B
            → Γ ⊢ t₂      ~ t₂′       ∶ A
            ----------------------------------
            → Γ ⊢ t₁ ∙ t₂ ~ t₁′ ∙ t₂′ ∶ B

    sim-lam : Γ , A ⊢ t   ~ t′   ∶ B
            ---------------------------------
            → Γ     ⊢ ƛ t ~ ƛ t′ ∶ A ⇒ B

    sim-box : Γ ■ ⊢ t     ~ t′     ∶ A
            ----------------------------
            → Γ   ⊢ box t ~ box t′ ∶ □ A
    
    sim-unbox : Γ   ⊢ t       ~ t′       ∶ □ A
              --------------------------------
              → Γ ■ ⊢ unbox t ~ unbox t′ ∶ A

ni : Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ →β t₁′ 
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
ni sim β■ = {!   !}
ni sim βƛ = {!   !}
ni sim (ξappl step) = {!   !}
ni sim (ξappr step) = {!   !}
ni sim (ξbox step) = {!   !}
ni sim (ξunbox step) = {!   !}
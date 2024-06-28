module Simul where
open import Base
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Bool 
open import Data.Nat
open import Data.Product renaming (_,_ to _⸲_)
open import Subst

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Γ′ Δ Δ₁ Δ₂ Γ₁ Γ₂ θ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-nat : (n : ℕ) 
            ----------
            → Γ ⊢ nat n ~ nat n ∶ Nat

    sim-mon : (t  : Γ ⊢ M A) 
            → (t′ : Γ ⊢ M A)
            ----------------
            → Γ ⊢ t ~ t′ ∶ M A

    sim-var : (x : A ∈ Γ)
            ---------------------------------
            → Γ ⊢ var x ~ var x ∶ A

    sim-app : Γ ⊢ t₁      ~ t₁′       ∶ A ⇒ B
            → Γ ⊢ t₂      ~ t₂′       ∶ A
            ----------------------------------
            → Γ ⊢ t₁ ∙ t₂ ~ t₁′ ∙ t₂′ ∶ B

    sim-lam : Γ , A ⊢ t   ~ t′   ∶ B
            ---------------------------------
            → Γ     ⊢ ƛ t ~ ƛ t′ ∶ A ⇒ B


sim-refl : (t : Γ ⊢ A) → Γ ⊢ t ~ t ∶ A
sim-refl (nat n)       = sim-nat n
sim-refl (var x)       = sim-var x
sim-refl (η t)         = sim-mon (η t) (η t)
sim-refl (ƛ t)         = sim-lam (sim-refl t)
sim-refl (l ∙ r)       = sim-app (sim-refl l) (sim-refl r)
sim-refl (bind t of u) = sim-mon _ _


sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit t₁         t₂        (sim-nat n)         = refl
sit t₁         t₂        (sim-mon _ _)       = refl
sit t₁         t₂        (sim-var x)         = refl
sit (ƛ t₁)     (ƛ t₂)    (sim-lam sim)       with sit t₁ t₂ sim 
... | refl = refl
sit (l₁ ∙ r₁)  (l₂ ∙ r₂) (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
... | refl = refl


sit′ : {t₁ t₂ : Γ ⊢ B} → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit′ {t₁ = t₁} {t₂ = t₂} = sit t₁ t₂ 

-- Simulation extended pointwise to substitutions
infix 2 _,_⊢_~_
data _,_⊢_~_ : (Δ Γ : Context) → Δ ⇉ Γ → Δ ⇉ Γ → Set where
    simσ-ε : Δ , ∅ ⊢ ε ~ ε

    simσ-• : Δ , Γ ⊢ σ  ~ τ
           → Δ     ⊢ t₁ ~ t₂ ∶ A
           -----------------------------------
           → Δ , (Γ , A) ⊢ (σ • t₁) ~ (τ • t₂)

 
simσ-refl : Δ , Γ ⊢ σ ~ σ
simσ-refl {σ = ε}         = simσ-ε
simσ-refl {σ = σ • t}     = simσ-• simσ-refl (sim-refl t)
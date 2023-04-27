module Simul where
open import Base
open import LFExt
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
    Γ Γ′ Δ Γ₁ Γ₂ θ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-nat : (n : ℕ) 
            ----------
            → Γ ⊢ nat n ~ nat n ∶ Nat

    sim-lock : Γ is Γ₁ ■ ∷ Γ₂
             → (t  : Γ ⊢ A) 
             → (t′ : Γ ⊢ A)
             ------------------
             → Γ ⊢ t ~ t′ ∶ A

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

    sim-box : Γ ■ ⊢ t     ~ t′     ∶ A
            ----------------------------
            → Γ   ⊢ box t ~ box t′ ∶ □ A
    
    sim-unbox : Γ   ⊢ t                    ~ t′                    ∶ □ A
              ----------------------------------------------------------
              → Γ ■ ⊢ unbox {ext = □ext} t ~ unbox {ext = □ext} t′ ∶ A

sim-refl : (t : Γ ⊢ A) → Γ ⊢ t ~ t ∶ A
sim-refl (nat n) = sim-nat n
sim-refl (var x) = sim-var x
sim-refl (ƛ t)   = sim-lam (sim-refl t)
sim-refl (box t) = sim-box (sim-refl t)
sim-refl (l ∙ r) = sim-app (sim-refl l) (sim-refl r)
sim-refl (unbox {ext = e} t) 
    = sim-lock e (unbox t) (unbox t)

-- Simulation implies typing, used to coax agda into unifying types of simulations.
sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit t₁         t₂         (sim-nat n)                               = refl
sit t₁         t₂         (sim-lock x _ _)                          = refl
sit t₁         t₂         (sim-var x)                               = refl
sit (ƛ t₁)     (ƛ t₂)     (sim-lam sim)       rewrite sit t₁ t₂ sim = refl
sit (box t₁)   (box t₂)   (sim-box sim)       rewrite sit t₁ t₂ sim = refl
sit (l₁ ∙ r₁)  (l₂ ∙ r₂)  (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
... | refl = refl
sit (unbox t₁) (unbox t₂) (sim-unbox sim)     with sit t₁ t₂ sim 
... | refl = refl

-- Simulation extended pointwise to substitutions
infix 2 _,_⊢_~_
data _,_⊢_~_ : (Γ Δ : Context) → Γ ⇉ Δ → Γ ⇉ Δ → Set where
    simσ-ε : Γ , ∅ ⊢ ε ~ ε

    simσ-p : (w : Γ ⊆ Γ′)
           --------------
           → Γ′ , Γ ⊢ wk w ~ wk w

    simσ-■ : Γ   , Δ   ⊢ σ    ~ τ 
           -------------------------
           → Γ ■ , Δ ■ ⊢ σ •■ ~ τ •■ 

    simσ-• : Γ , Δ ⊢ σ  ~ τ
           → Γ     ⊢ t₁ ~ t₂ ∶ A
           -----------------------------------
           → Γ , (Δ , A) ⊢ (σ • t₁) ~ (τ • t₂)

simσ-refl : Γ , Δ ⊢ σ ~ σ
simσ-refl {σ = ε}     = simσ-ε
simσ-refl {σ = wk x}  = simσ-p x
simσ-refl {σ = σ •■}  = simσ-■ simσ-refl
simσ-refl {σ = σ • t} = simσ-• simσ-refl (sim-refl t)
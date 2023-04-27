module Simul where
open import Base
open import Terms
open import Trans
open import Subst
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Function
open import Data.Bool hiding (T)
open import Data.Nat
open import Data.Product renaming (_,_ to _⸲_)

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ l₁ l₂ r₁ r₂ : _ ⊢ _
    x y : _ ∈ _
    n m : ℕ
    A B : Type
    Γ Γ′ Δ Γ₁ Γ₂ θ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

infix 2 _≈_
-- Same constructor proof, for syntax directedness.
-- Saves us from having to make a bunch of rules for each constructor.
data _≈_ : Γ ⊢ A → Γ ⊢ A → Set where
    -- For some reason Agda can't figure out Γ here??
    eqc-nat : _≈_ {Γ = Γ} (nat n) (nat m)
    -- eqc-var : var x     ≈ var y
    eqc-lam : ƛ t₁      ≈ ƛ t₂ 
    eqc-eta : η t₁      ≈ η t₂
    eqc-app : l₁ ∙ r₁   ≈ l₂ ∙ r₂
    eqc-bnd : bnd a₁ t₁ ≈ bnd a₂ t₂

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-box : (t₁ : Γ ⊢ T A)
            → (t₂ : Γ ⊢ T A)
            → t₁ ≈ t₂
            -----------------------
            → Γ ⊢ t₁ ~ t₂ ∶ T A

    sim-nat : (n : ℕ) 
            ----------
            → Γ ⊢ nat n ~ nat n ∶ Nat

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
sim-refl (η t)     = sim-box (η t) (η t) eqc-eta
sim-refl (nat x)   = sim-nat x
sim-refl (var x)   = sim-var x
sim-refl (ƛ t)     = sim-lam (sim-refl t)
sim-refl (l ∙ r)   = sim-app (sim-refl l) (sim-refl r)
sim-refl (bnd a t) = sim-box (bnd a t) (bnd a t) eqc-bnd

private module lemmas where
    -- sit-prot : (sim : Γ ⊢ t₁ ~ t₂ ∶ A) → sim ≡ sim-prot → A ≡ T B
    -- sit-prot sim refl = ?
    -- sit-¬nat : ¬ ( Γ ⊢ (nat n) ~ t ∶ T A )
    -- sit-¬nat p = {!   !}

open lemmas

-- Simulation implies typing, used to coax agda into unifying types of simulations.
sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit _ _ (sim-box _ _ _) = refl
----------------------------
sit _ _ (sim-nat n) = refl
sit _ _ (sim-var x) = refl
--------------------------
sit (l₁ ∙ r₁)   (l₂ ∙ r₂)   (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
... | refl = refl
sit (ƛ t₁)      (ƛ t₂)      (sim-lam sim)       with sit t₁ t₂ sim 
... | refl = refl

-- Simulation extended pointwise to substitutions
infix 2 _,_⊢_~_
data _,_⊢_~_ : (Γ Δ : Context) → Γ ⇉ Δ → Γ ⇉ Δ → Set where
    simσ-ε : Γ , ∅ ⊢ ε ~ ε

    simσ-p : (w : Γ ⊆ Γ′)
           --------------
           → Γ′ , Γ ⊢ wk w ~ wk w

    simσ-• : Γ , Δ ⊢ σ  ~ τ
           → Γ     ⊢ t₁ ~ t₂ ∶ A
           -----------------------------------
           → Γ , (Δ , A) ⊢ (σ • t₁) ~ (τ • t₂)

simσ-refl : Γ , Δ ⊢ σ ~ σ
simσ-refl {σ = ε}     = simσ-ε
simσ-refl {σ = wk x}  = simσ-p x
simσ-refl {σ = σ • t} = simσ-• simσ-refl (sim-refl t) 
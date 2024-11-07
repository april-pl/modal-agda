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
    Γ Γ′ Δ Δ₁ Δ₂ Γ₁ Γ₂ θ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-zer : Γ ⊢ zer ~ zer ∶ Nat

    sim-suc : Γ ⊢ t     ~ t′     ∶ Nat
            --------------------------
            → Γ ⊢ suc t ~ suc t′ ∶ Nat

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

    sim-box : {t t′ : Γ ⊢ □ A}  
            → Γ ⊢ t ~ t′ ∶ □ A
    
    -- Morally this should take an argument of type Γ₁ ⊢ t ~ t′ ∶ □ A
    -- But this is trivial by sim-box and it makes some things easier to omit it
    sim-unbox : {t t′ : Γ₁ ⊢ □ A}  
              → {ext : Γ is Γ₁ ■ ∷ Γ₂}
              ----------------------------------------------------------
              → Γ ⊢ unbox {ext = ext} t ~ unbox {ext = ext} t′ ∶ A

sim-refl : (t : Γ ⊢ A) → Γ ⊢ t ~ t ∶ A
sim-refl zer     = sim-zer
sim-refl (suc n) = sim-suc (sim-refl n)
sim-refl (var x) = sim-var x
sim-refl (ƛ t)   = sim-lam (sim-refl t)
sim-refl (box t) = sim-box
sim-refl (l ∙ r) = sim-app (sim-refl l) (sim-refl r)
sim-refl (unbox {ext = e} t) 
    = sim-unbox 

-- Simulation implies typing, used to coax agda into unifying types of simulations.
sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit _          _          sim-zer     = refl
sit _          _          (sim-suc n) = refl
sit _          _          (sim-var x) = refl
sit _          _          sim-box     = refl
sit (l₁ ∙ r₁)  (l₂ ∙ r₂)  (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
... | refl = refl
sit (ƛ t₁)     (ƛ t₂)     (sim-lam sim)       rewrite sit t₁ t₂ sim = refl
sit (unbox t₁) (unbox t₂) sim-unbox = refl

sit′ : {t₁ t₂ : Γ ⊢ B} → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit′ {t₁ = t₁} {t₂ = t₂} = sit t₁ t₂ 

-- Simulation extended pointwise to substitutions
infix 2 _,_⊢_~_
data _,_⊢_~_ : (Δ Γ : Context) → Δ ⇉ Γ → Δ ⇉ Γ → Set where
    simσ-ε : Δ , ∅ ⊢ ε ~ ε

    simσ-• : {σ τ : Δ ⇉ Γ}
           → Δ , Γ ⊢ σ  ~ τ
           → Δ     ⊢ t₁ ~ t₂ ∶ A
           -----------------------------------
           → Δ , (Γ , A) ⊢ (σ • t₁) ~ (τ • t₂)

    simσ-■ : {σ τ : Δ₁ ⇉ Γ} 
           → Δ₁ , Γ  ⊢ σ         ~ τ
           → (w : Δ is Δ₁ ■ ∷ Δ₂)
           ---------------------------------
           → Δ , Γ ■ ⊢ σ •[ w ]■ ~ τ •[ w ]■

simσ-refl : Δ , Γ ⊢ σ ~ σ
simσ-refl {σ = ε}         = simσ-ε
simσ-refl {σ = σ • t}     = simσ-• simσ-refl (sim-refl t)
simσ-refl {σ = σ •[ w ]■} = simσ-■ simσ-refl w

module Lemmas where
    sim-weak : (t₁ t₂ : Γ ⊢ A) 
             → (wk : Γ ⊆ Δ) 
             → Γ ⊢ t₁ ~ t₂ ∶ A 
             → Δ ⊢ weakening wk t₁ ~ weakening wk t₂ ∶ A
    sim-weak _       _       wk sim-zer           = sim-zer
    sim-weak (suc n) (suc m) wk (sim-suc sim)     = sim-suc (sim-weak n m wk sim)
    sim-weak t₁      t₂      wk sim-box           = sim-box 
    
    sim-weak _ _ wk (sim-var x) = sim-var (Γ-weak wk x)

    sim-weak (ƛ t₁) (ƛ t₂) wk (sim-lam sim) = sim-lam (sim-weak t₁ t₂ (⊆-keep wk) sim)
    
    sim-weak (l₁ ∙ r₁)  (l₂ ∙ r₂) wk (sim-app simₗ simᵣ) with sit′ simₗ | sit′ simᵣ
    ... | refl | refl = sim-app (sim-weak l₁ l₂ wk simₗ) 
                                (sim-weak r₁ r₂ wk simᵣ)
    
    sim-weak (unbox {ext} t₁) (unbox t₂) wk sim-unbox = sim-unbox

    sim-weak′ : {t₁ t₂ : Γ ⊢ A} 
              → {wk : Γ ⊆ Δ}
              → Γ ⊢ t₁ ~ t₂ ∶ A 
              → Δ ⊢ weakening wk t₁ ~ weakening wk t₂ ∶ A
    sim-weak′ {t₁} {t₂} {wk} sim = sim-weak t₁ t₂ wk sim

    simσ-weak : Δ       , Γ       ⊢ σ₁     ~ σ₂
              → (Δ , A) , Γ       ⊢ wk σ₁  ~ wk σ₂
    simσ-weak simσ-ε          = simσ-ε
    simσ-weak (simσ-• simσ x) = simσ-• (simσ-weak simσ) (sim-weak′ x) 
    simσ-weak (simσ-■ simσ w) = simσ-■ simσ (is-ext w)
  
    lemma-σ+ : Γ       , Δ       ⊢ σ            ~ τ
             → (Γ , A) , (Δ , A) ⊢ σ+ {A = A} σ ~ σ+ {A = A} τ
    lemma-σ+ simσ-ε = simσ-• simσ-ε (sim-var Z) 
    lemma-σ+ (simσ-• sim x) = 
        simσ-• (simσ-• (simσ-weak sim) (sim-weak′ x)) (sim-var Z)   
    lemma-σ+ (simσ-■ simσ w) = simσ-• (simσ-■ simσ (is-ext w)) (sim-var Z)   

    simσ-←■ : Γ    , Δ    ⊢ σ        ~ τ
            → ←■ Γ , ←■ Δ ⊢ sub-←■ σ ~ sub-←■ τ
    simσ-←■ simσ-ε          = simσ-ε 
    simσ-←■ (simσ-• simσ t) = simσ-←■ simσ
    simσ-←■ (simσ-■ simσ w ) with is∷-←■ w 
    ... | refl = simσ
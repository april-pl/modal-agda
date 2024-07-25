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
    
    sim-unbox : {ext : Γ is Γ₁ ■ ∷ Γ₂} 
              → Γ₁   ⊢ t                    ~ t′                    ∶ □ A
              ----------------------------------------------------------
              → Γ ⊢ unbox {ext = ext} t ~ unbox {ext = ext} t′ ∶ A

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

    simσ-■ : Δ₁ , Γ  ⊢ σ         ~ τ
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
    sim-weak _ _ wk (sim-nat n) = sim-nat n
    sim-weak _ _ wk (sim-var x) = sim-var (Γ-weak wk x)

    sim-weak (ƛ t₁) (ƛ t₂) wk (sim-lam sim) = sim-lam (sim-weak t₁ t₂ (⊆-keep wk) sim)
    
    sim-weak (l₁ ∙ r₁)  (l₂ ∙ r₂) wk (sim-app simₗ simᵣ) with sit′ simₗ | sit′ simᵣ
    ... | refl | refl = sim-app (sim-weak l₁ l₂ wk simₗ) 
                                (sim-weak r₁ r₂ wk simᵣ)
                                
    sim-weak t₁ t₂ wk (sim-lock p _ _) with is∷-Δweak p wk 
    ... | p′ = sim-lock p′ (weakening wk t₁) (weakening wk t₂)
    
    sim-weak (box t₁)   (box t₂)   wk (sim-box sim)   = sim-box (sim-weak t₁ t₂ (⊆-lock wk) sim)
    sim-weak (unbox {ext} t₁) (unbox t₂) wk (sim-unbox sim) with is∷-Δweak ext wk
    ... | ext′ = sim-unbox {ext = ext′} (sim-weak t₁ t₂ (is∷-←■weak ext wk) sim)

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
module Simul where
open import Base
open import LFExt
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Bool 
open import Data.Product renaming (_,_ to _⸲_)
open import Subst

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    σ σ₁ σ₂ : Sub _ _
    A B : Type
    Γ Γ′ Δ Δ′ Γ₁ Γ₂  : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
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

-- Simulation implies typing...
-- Seriously, can't agda figure this one out itself?
sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit t₁         t₂         (sim-lock x _ _)                          = refl
sit t₁         t₂         (sim-var x)                               = refl
sit (ƛ t₁)     (ƛ t₂)     (sim-lam sim)       rewrite sit t₁ t₂ sim = refl
sit (box t₁)   (box t₂)   (sim-box sim)       rewrite sit t₁ t₂ sim = refl
sit (l₁ ∙ r₁)  (l₂ ∙ r₂)  (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
... | refl = refl
sit (unbox t₁) (unbox t₂) (sim-unbox sim)     with sit t₁ t₂ sim 
... | refl = refl

weakening~ : (wk : Γ ⊆ Δ) 
           → Γ ⊢ t₁ ~ t₂ ∶ A 
           → Δ ⊢ (weakening wk t₁) ~ (weakening wk t₂) ∶ A
weakening~ wk (sim-lock ext t₁ t₂) = sim-lock (is∷-Δweak ext wk) (weakening wk t₁) (weakening wk t₂)
weakening~ wk (sim-var x)          = sim-var (Γ-weak wk x)
weakening~ wk (sim-app simₗ simᵣ)  = sim-app (weakening~ wk simₗ) (weakening~ wk simᵣ)
weakening~ wk (sim-lam sim)        = sim-lam (weakening~ (⊆-keep wk) sim)
weakening~ wk (sim-box sim)        = sim-box (weakening~ (⊆-lock wk) sim)
weakening~ wk (sim-unbox {t = t₁} {t₂} {□ext = ext} sim) with sit _ _ sim
... | refl = sim-lock (is∷-Δweak ext wk) (weakening wk (unbox t₁)) (weakening wk (unbox t₂)) 

-- Simulation, extended pointwise to substitutions
infix 2 _,_⊢σ_~_
data _,_⊢σ_~_ : (Γ Δ : Context) → Sub Γ Δ → Sub Γ Δ → Set where
    simσ-base : ∅ , ∅ ⊢σ sub-base ~ sub-base

    simσ-lock : Γ   , Δ   ⊢σ σ₁            ~ σ₂
              --------------------------------------
              → Γ ■ , Δ ■ ⊢σ (sub-lock σ₁) ~ (sub-lock σ₂)

    simσ-keep : Γ       , Δ       ⊢σ σ₁            ~ σ₂
              ----------------------------------------------------
              → (Γ , A) , (Δ , A) ⊢σ (sub-keep σ₁) ~ (sub-keep σ₂) 

    simσ-subs : Γ       , Δ ⊢σ σ₁               ~ σ₂
              → Δ           ⊢  t₁               ~ t₂ ∶ B
              ----------------------------------------------------
              → (Γ , B) , Δ ⊢σ (sub-subs σ₁ t₁) ~ (sub-subs σ₂ t₂)

    simσ-trim : Γ , Δ ⊢σ σ₁ ~ σ₂
              → (wk : Δ ⊆ Δ′)
              -----------------------------------------------
              → Γ , Δ′ ⊢σ (sub-trim σ₁ wk) ~ (sub-trim σ₂ wk)



    
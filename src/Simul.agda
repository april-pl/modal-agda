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
    A B : Type
    Γ Γ′ Δ Γ₁ Γ₂ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂
    σ σ₁ σ₂ τ : _ ⇉ _

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

weakening~ : (w : Γ ⊆ Δ) 
           → Γ ⊢ t₁ ~ t₂ ∶ A 
           → Δ ⊢ (weakening w t₁) ~ (weakening w t₂) ∶ A
weakening~ w (sim-lock ext t₁ t₂) = sim-lock (is∷-Δweak ext w) (weakening w t₁) (weakening w t₂)
weakening~ w (sim-var x)          = sim-var  (Γ-weak w x)
weakening~ w (sim-app simₗ simᵣ)  = sim-app  (weakening~ w simₗ) (weakening~ w simᵣ)
weakening~ w (sim-lam sim)        = sim-lam  (weakening~ (⊆-keep w) sim)
weakening~ w (sim-box sim)        = sim-box  (weakening~ (⊆-lock w) sim)
weakening~ w (sim-unbox {t = t₁} {t₂} {□ext = ext} sim) with sit _ _ sim
... | refl = sim-lock (is∷-Δweak ext w) (weakening w (unbox t₁)) (weakening w (unbox t₂)) 

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
module NonInterference where
open import Base
open import Terms
open import Trans
open import Subst
open import Simul
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Function
open import Data.Bool 
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _،_)

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Δ Δ′ Γ₁ Γ₂ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _ 

private module lemmas where
    lemma-st : (w : Δ′ ⊆ Δ) 
             → Γ , Δ  ⊢ σ ~ τ 
             ---------------------------------------
             → Γ , Δ′ ⊢ ⇉-st σ w ~ ⇉-st τ w
    lemma-st ⊆-empty simσ-ε = simσ-ε
    --------------------------------
    lemma-st ⊆-empty (simσ-p w₁) = simσ-ε
    lemma-st (⊆-drop w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-drop w) w₁)
    lemma-st (⊆-keep w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-keep w) w₁)
    ----------------------------------------------------------------
    lemma-st (⊆-drop w) (simσ-• simσ x) = lemma-st w simσ
    lemma-st (⊆-keep w) (simσ-• simσ x) = simσ-• (lemma-st w simσ) x

    lemma-≈ : Δ , Γ ⊢ σ ~ τ → t₁ ≈ t₂ → sub σ t₁ ≈ sub τ t₂
    lemma-≈ simσ eqc-nat = eqc-nat
    lemma-≈ simσ eqc-lam = eqc-lam
    lemma-≈ simσ eqc-eta = eqc-eta
    lemma-≈ simσ eqc-app = eqc-app
    lemma-≈ simσ eqc-bnd = eqc-bnd

open lemmas

{-# TERMINATING #-}
mutual 
    lemma-σ+ : Γ       , Δ       ⊢ σ            ~ τ
             → (Γ , A) , (Δ , A) ⊢ σ+ {A = A} σ ~ σ+ {A = A} τ

    ius : (t₁ t₂ : Γ ⊢ A)
        → (σ₁ σ₂ : Δ ⇉ Γ)
        -----------------------------------
        → Γ     ⊢ t₁          ~ t₂          ∶ A 
        → Δ , Γ ⊢ σ₁          ~ σ₂ 
        -----------------------------------
        → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A

    lemma-σ+ simσ-ε     = simσ-• simσ-ε                                (sim-var Z)
    lemma-σ+ (simσ-p w) = simσ-• (lemma-st w (simσ-p (⊆-drop ⊆-refl))) (sim-var Z)
    lemma-σ+ (simσ-• {σ = σ} {t₁ = t₁} {t₂ = t₂} simσ simₜ) with lemma-σ+ simσ
    ... | simσ-• simσ′ r = simσ-• (simσ-• simσ′ (ius t₁ t₂ p p simₜ simσ-refl)) r


    ius t₁      t₂      σ τ (sim-box _ _ eqc) simσ = sim-box (sub σ t₁) (sub τ t₂) (lemma-≈ simσ eqc)
    ius (nat n) (nat n) σ τ (sim-nat n)       simσ = sim-nat n
    ----------------------------------------------------------
    ius (l₁ ∙ r₁) (l₂ ∙ r₂) σ τ (sim-app simₗ simᵣ) simσ with sit _ _ simₗ | sit _ _ simᵣ
    ... | refl | refl = sim-app (ius  l₁ l₂ σ τ simₗ simσ) (ius r₁ r₂ σ τ simᵣ simσ)
    --------------------------------------------------------------------------------
    ius t₁ t₂ (wk w) (wk w) (sim-var Z)     (simσ-p w) = sim-var (Γ-weak w Z)
    ius t₁ t₂ (wk w) (wk w) (sim-var (S x)) (simσ-p w) =
        let w′ = ⊆-assoc (⊆-drop ⊆-refl) w
        in ius (var x) (var x) (wk w′) (wk w′) (sim-var x) (simσ-p w′)
        
    ius t₁ t₂ (σ • _) (τ • _) (sim-var Z)     (simσ-• simσ simᵤ) = simᵤ
    ius t₁ t₂ (σ • _) (τ • _) (sim-var (S x)) (simσ-• simσ simᵤ) =
        ius (var x) (var x) (⇉-st σ ⊆-refl) (⇉-st τ ⊆-refl) (sim-var x) (lemma-st ⊆-refl simσ)
    -------------------------------------------------------------
    ius (ƛ b₁) (ƛ b₂) σ τ (sim-lam simₜ) simσ with sit b₁ b₂ simₜ
    ... | refl = sim-lam (ius b₁ b₂ (σ+ σ) (σ+ τ) simₜ (lemma-σ+ simσ))

-- Non-interference for MMM
ni : Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ →β t₁′
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))

-- ni (sim-box .((ƛ _) ∙ _) _ eqc-app) βƛ = {!   !}
-- ni (sim-app sim sim₁) βƛ = {!   !}
-- ni sim βbind = {!   !}
-- ni sim (ξappl step) = {!   !}
-- ni sim (ξappr step) = {!   !}
-- ni sim (ξbind step) = {!   !}

ni (sim-box (f₁ ∙ x₁) t (eqc-app {l₂ = f₂} {x₂})) βƛ = {!   !} ، {! βƛ !} ، {!   !}
ni (sim-box .(bnd (η _) _) _ _) βbind = {!   !}

ni (sim-box (l₁ ∙ r₁) _ (eqc-app {l₂ = l₂} {r₂})) (ξappl step) with ni {!   !} step
... | a = {! l₂ ∙ r₂ !} ، {!   !} ، {!   !}

ni (sim-box .(_ ∙ _) _ _) (ξappr step) = {!   !}
ni (sim-box .(bnd _ _) _ _) (ξbind step) = {!   !}

ni (sim-box _ _ _) a = {!   !}

ni (sim-app {t₁ = f₁} {f₂} {t₂ = x₁} {x₂} simƛ simᵣ) βƛ with simƛ 
... | sim-lam {t = b₁} {b₂} sim∙ = b₂ [ x₂ ] ، βƛ 
                                 ، ius b₁ b₂ (sub-refl • x₁) (sub-refl • x₂) sim∙ (simσ-• simσ-refl simᵣ)
                                 
ni (sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappl step) 
                                    with sit _ _ simₗ | sit _ _ simᵣ
... | refl | refl                   with ni simₗ step 
... | l₂′ ، βl₂ ، ind               with sit _ _ ind 
... | refl = l₂′ ∙ r₂ ، ξappl βl₂ ، sim-app ind simᵣ

ni (sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappr step) 
                                    with sit _ _ simₗ | sit _ _ simᵣ
... | refl | refl                   with ni simᵣ step 
... | r₂′ ، βr₂ ، ind               with sit _ _ ind 
... | refl = l₂ ∙ r₂′ ، ξappr βr₂ ، sim-app simₗ ind  
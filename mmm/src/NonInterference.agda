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

open lemmas

-- Non-interference for MMM
ni : Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ →β t₁′
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
ni sim-prot βƛ = {!  !} 
               ، {!   !} 
               ، sim-prot
ni (sim-app sim sim₁) βƛ = {!   !}

ni sim-prot βbind = {!  !} ، {!   !} ، sim-prot

ni sim-prot (ξappl step) = {!   !}
ni (sim-app simₗ simᵣ) (ξappl step) = {!   !}
ni sim (ξappr step) = {!   !}
ni sim (ξbind step) = {!   !} 
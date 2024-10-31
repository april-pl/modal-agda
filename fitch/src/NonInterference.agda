module NonInterference where
open import Base
open import LFExt
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Function
open import Data.Bool 
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _،_; _×_ to _×′_)
open import Subst
open import Simul
open Lemmas

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Δ Δ′ Γ₁ Γ₂ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _ 

ius : ¬■ Γ
    → ¬■ Δ
    → (t₁ t₂ : Γ ⊢ A)
    → (σ₁ σ₂ : Δ ⇉ Γ)
    -----------------------------------
    → Γ     ⊢ t₁          ~ t₂          ∶ A 
    → Δ , Γ ⊢ σ₁          ~ σ₂ 
    -----------------------------------
    → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A

ius _  _  _       _       σ₁ σ₂ sim-zer       simσ = sim-zer
ius p₁ p₂ (suc n) (suc m) σ₁ σ₂ (sim-suc sim) simσ = sim-suc (ius p₁ p₂ n m σ₁ σ₂ sim simσ)

ius p₁ p₂ t₁ t₂ σ₁ σ₂ (sim-lock x _ _) simσ = ⊥-elim (¬■-■ p₁ x)

ius p₁       p₂ _ _ _         _         (sim-var Z)     (simσ-• _ sim)    = sim
ius (¬■, p₁) p₂ _ _ (σ₁ • u₁) (σ₂ • u₂) (sim-var (S x)) (simσ-• simσ sim) = 
    ius p₁ p₂ (var x) (var x) σ₁ σ₂ (sim-var x) simσ

ius p₁ p₂ (l₁ ∙ r₁) (l₂ ∙ r₂) σ₁ σ₂ (sim-app simₗ simᵣ) simσ with sit′ simₗ | sit′ simᵣ
... | refl | refl = sim-app (ius p₁ p₂ l₁ l₂ σ₁ σ₂ simₗ simσ) 
                            (ius p₁ p₂ r₁ r₂ σ₁ σ₂ simᵣ simσ) 

ius p₁ p₂ (ƛ t₁) (ƛ t₂) σ₁ σ₂ (sim-lam sim) simσ with sit′ sim
... | refl = sim-lam (ius (¬■, p₁) (¬■, p₂) t₁ t₂ (σ+ σ₁) (σ+ σ₂) sim (lemma-σ+ simσ))

ius p₁ p₂ (box t₁) (box t₂) σ₁ σ₂ (sim-box sim) simσ with sit′ sim 
... | refl = sim-box (sim-lock is-nil (sub (σ₁ •■) t₁) (sub (σ₂ •■) t₂))

ius p₁ p₂ (unbox _) (unbox _) _ _ (sim-unbox {ext} _) _ = ⊥-elim (is∷-¬¬■ ext p₁)

           
-- Non-interference for the Fitch calculus
bisim : ¬■ Γ
   → Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ ↝ t₁′ 
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ ↝ t₂′) ×′ (Γ ⊢ t₁′ ~ t₂′ ∶ A))
bisim prf (sim-lock ext _ _) _    = ⊥-elim (is∷-¬¬■ ext prf) 
bisim prf sim (ξunbox {ext} step) = ⊥-elim (is∷-¬¬■ ext prf) 
bisim prf (sim-app (sim-lock ext _ _) _) _ 
    =  ⊥-elim (is∷-¬¬■ ext prf) 

bisim {t₁ = (ƛ t₁) ∙ r₁} {t₂ = (ƛ t₂) ∙ r₂} p (sim-app (sim-lam simₗ) simᵣ) βƛ 
    with sit′ simₗ | sit′ simᵣ 
... | refl | refl = t₂ [ r₂ ] 
                  ، βƛ 
                  ، ius (¬■, p) p 
                        t₁ t₂ (Subst.id • r₁) (Subst.id • r₂) 
                        simₗ 
                        (simσ-• simσ-refl simᵣ)

bisim {t₁ = l₁ ∙ r₁} {t₂ = l₂ ∙ r₂} p sim@(sim-app simₗ simᵣ) (ξappl step)
                         with  sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl with bisim p simₗ step
... | l₂′ ، step ، sim′ = l₂′ ∙ r₂ ، ξappl step ، sim-app sim′ simᵣ
 
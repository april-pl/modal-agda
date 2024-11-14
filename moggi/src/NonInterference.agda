module NonInterference where
open import Base
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _،_; _×_ to _×′_)
open import Normalisation
open import Subst
open import Simul
open Simul.Lemmas

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Δ Δ′ Γ₁ Γ₂ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _ 

ius : (t₁ t₂ : Γ ⊢ A)
    → (σ₁ σ₂ : Δ ⇉ Γ)
    -----------------------------------
    → Γ     ⊢ t₁          ~ t₂          ∶ A 
    → Δ , Γ ⊢ σ₁          ~ σ₂ 
    -----------------------------------
    → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A
    
ius _ _ σ₁ σ₂ sim-one simσ = sim-one
-------------------------------------------------------------------------------
ius _ _ σ₁ σ₂ (sim-mon t₁ t₂) simσ = sim-mon (sub σ₁ t₁) (sub σ₂ t₂)
--------------------------------------------------------------------
ius _ _ _       _       (sim-var Z)     (simσ-• simσ x) = x
ius _ _ (σ • t) (τ • u) (sim-var (S x)) (simσ-• simσ _) 
    = ius (var x) (var x) σ τ (sim-var x) simσ
----------------------------------------------
ius (l₁ ∙ r₁) (l₂ ∙ r₂) σ₁ σ₂ (sim-app simₗ simᵣ) simσ with sit′ simₗ | sit′ simᵣ
... | refl | refl = sim-app (ius l₁ l₂ σ₁ σ₂ simₗ simσ) 
                            (ius r₁ r₂ σ₁ σ₂ simᵣ simσ)
-------------------------------------------------------
ius (ƛ t₁) (ƛ t₂) σ₁ σ₂ (sim-lam sim) simσ with sit′ sim
... | refl = sim-lam (ius t₁ t₂ (σ+ σ₁) (σ+ σ₂) sim (lemma-σ+ simσ))
------------------------------------------------------
ius (⟨ l₁ , r₁ ⟩) (⟨ l₂ , r₂ ⟩) σ₁ σ₂ (sim-mul sim sim₁) simσ 
    = sim-mul (ius l₁ l₂ σ₁ σ₂ sim simσ) (ius r₁ r₂ σ₁ σ₂ sim₁ simσ)
--------------------------------------------------------------------
ius (π₁ t₁) (π₁ t₂) σ₁ σ₂ (sim-pi1 sim) simσ with sit′ sim
... | refl = sim-pi1 (ius t₁ t₂ σ₁ σ₂ sim simσ)
ius (π₂ t₁) (π₂ t₂) σ₁ σ₂ (sim-pi2 sim) simσ with sit′ sim
... | refl = sim-pi2 (ius t₁ t₂ σ₁ σ₂ sim simσ)
-----------------------------------------------
ius (inl t₁) (inl t₂) σ₁ σ₂ (sim-inl sim) simσ = sim-inl (ius t₁ t₂ σ₁ σ₂ sim simσ)
ius (inr t₁) (inr t₂) σ₁ σ₂ (sim-inr sim) simσ = sim-inr (ius t₁ t₂ σ₁ σ₂ sim simσ)
----------
ius (case t₁ of l₁ , r₁) (case t₂ of l₂ , r₂) σ₁ σ₂ (sim-cof sim simₗ simᵣ) simσ 
    = sim-cof (ius t₁ t₂ σ₁ σ₂ sim simσ) 
              (ius l₁ l₂ (σ+ σ₁) (σ+ σ₂) simₗ (lemma-σ+ simσ))
              (ius r₁ r₂ (σ+ σ₁) (σ+ σ₂) simᵣ (lemma-σ+ simσ))

ius (fold B t₁)   (fold B t₂)   σ₁ σ₂ (sim-fold sim) simσ   = sim-fold (ius t₁ t₂ σ₁ σ₂ sim simσ) 
ius (unfold _ refl t₁) (unfold _ refl t₂) σ₁ σ₂ (sim-unfold _ refl sim) simσ = sim-unfold _ refl (ius _ _ σ₁ σ₂ sim simσ) 

-- Non-interference relation is a bisimulation      
bisim : (t₁ t₂ : Γ ⊢ A)
      → pure A
      → Γ ⊢ t₁ ~ t₂ ∶ A 
      → t₁ ↝ t₁′ 
      ------------------------------------------------------
      → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ ↝ t₂′) ×′ (Γ ⊢ t₁′ ~ t₂′ ∶ A))

bisim ((ƛ t₁) ∙ r₁) ((ƛ t₂) ∙ r₂) p (sim-app (sim-lam simₗ) simᵣ) βƛ 
    with sit′ simₗ | sit′ simᵣ 
... | refl | refl = t₂ [ r₂ ] 
                  ، βƛ 
                  ، ius t₁ t₂ 
                       (Subst.id • r₁) (Subst.id • r₂) 
                       simₗ 
                       (simσ-• simσ-refl simᵣ)

bisim (l₁ ∙ r₁) (l₂ ∙ r₂) p sim@(sim-app simₗ simᵣ) (ξappl step)
                         with  sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl with bisim l₁ l₂ (p⇒ p) simₗ step
... | l₂′ ، step ، sim′ = l₂′ ∙ r₂ ، ξappl step ، sim-app sim′ simᵣ

bisim (case inl t₁ of l₁ , r₁) (case inl t₂ of l₂ , r₂) p (sim-cof (sim-inl sim) simₗ simᵣ) βinl 
            with sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl = l₂ [ t₂ ] ، βinl ، ius l₁ l₂ (id • t₁) (id • t₂) simₗ (simσ-• simσ-refl sim)

bisim (case inr t₁ of l₁ , r₁) (case inr t₂ of l₂ , r₂) p (sim-cof (sim-inr sim) simₗ simᵣ) βinr 
            with sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl = r₂ [ t₂ ] ، βinr ، ius r₁ r₂ (id • t₁) (id • t₂) simᵣ (simσ-• simσ-refl sim)

bisim (π₁ ⟨ l₁ , r₁ ⟩) (π₁ ⟨ l₂ , r₂ ⟩) p (sim-pi1 (sim-mul simₗ simᵣ)) βπ₁
    = l₂ ، βπ₁ ، simₗ
bisim (π₂ ⟨ l₁ , r₁ ⟩) (π₂ ⟨ l₂ , r₂ ⟩) p (sim-pi2 (sim-mul simₗ simᵣ)) βπ₂
    = r₂ ، βπ₂ ، simᵣ

bisim (case t₁ of l₁ , r₁) (case t₂ of l₂ , r₂) p (sim-cof sim sim₁ sim₂) (ξcase step) 
           with bisim t₁ t₂ p+ sim step 
... | t₂′ ، step′ ، sim′ = case t₂′ of l₂ , r₂ ، ξcase step′ ، sim-cof sim′ sim₁ sim₂
bisim (π₁ t₁) (π₁ t₂) p (sim-pi1 sim) (ξπ₁ step) 
           with sit′ sim
... | refl with bisim t₁ t₂ p× sim step 
... | t₂′ ، step′ ، sim′ = π₁ t₂′ ، ξπ₁ step′ ، sim-pi1 sim′

bisim (π₂ t₁) (π₂ t₂) p (sim-pi2 sim) (ξπ₂ step) 
           with sit′ sim
... | refl with bisim t₁ t₂ p× sim step 
... | t₂′ ، step′ ، sim′ = π₂ t₂′ ، ξπ₂ step′ ، sim-pi2 sim′

bisim (unfold B .refl (fold B t₁)) (unfold B .refl (fold B t₂)) p (sim-unfold B .refl (sim-fold sim)) βunfold 
    = t₂ ، βunfold ، sim

bisim (unfold B q₁ t₁) (unfold B q₂ t₂) p (sim-unfold B q₃ sim) (ξunfold step q₄) with bisim t₁ t₂ pμ sim step 
... | t₂′ ، step′ ، sim′ = unfold B q₁ t₂′ ، ξunfold step′ q₁ ، sim-unfold _ q₁ sim′


-- Multi-step bisimulation
bisim⋆ : pure A 
       → Γ ⊢ t₁ ~ t₂ ∶ A 
       → t₁ ↝⋆ t₁′ 
       ------------------------------------------------------
       → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ ↝⋆ t₂′) ×′ (Γ ⊢ t₁′ ~ t₂′ ∶ A))
bisim⋆ {t₂ = t₂} p sim ⋆refl = t₂ ، ⋆refl ، sim
bisim⋆ p sim (⋆step step)       with bisim _ _ p sim step
... | p′ ، sim′ ، step′    = p′ ، ⋆step sim′ ، step′
bisim⋆ p sim (⋆trns steps step) with bisim⋆ p sim steps 
... | t₂′ ، steps′ ، sim′        with bisim _ _ p sim′ step
... | t₂′′ ، step′ ، sim′′ = t₂′′ ، ⋆trns steps′ step′ ، sim′′


non-interference : (v : ∅       ⊢ Bool)
                 → (V : ∅ , T A ⊢ Bool) 
                 → (t : ∅       ⊢ T A)
                 → (u : ∅       ⊢ T A)
                 → V [ t ] ⇓ v
                 -------------
                 → V [ u ] ⇓ v 
non-interference v V t u V[t]-reduces = 
    let stepsₗ ، v-value             = V[t]-reduces
        t~u                          = sim-mon t u
        V~V                          = sim-refl V
        V[t]~V[u]                    = ius V V (id • t) (id • u) V~V (simσ-• simσ-ε t~u)
        V[u]′ ، stepsᵣ ، v~V[u]′      = bisim⋆ p+ V[t]~V[u] stepsₗ
        V[u]′-value                  = sim-value v V[u]′ v~V[u]′ v-value
        v≡V[u]′                      = ind-eql v V[u]′ v-value V[u]′-value v~V[u]′
        
        V[u]↝⋆v                     = subst (λ p → V [ u ] ↝⋆ p) (sym v≡V[u]′) stepsᵣ
    in V[u]↝⋆v ، proj₂ V[t]-reduces      
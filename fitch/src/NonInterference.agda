module NonInterference where
open import Base
open import LFExt
open import Terms
open import Trans
open import Normalisation
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
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
    
ius : ¬■ Γ
    → (t₁ t₂ : Γ ⊢ A)
    → (σ₁ σ₂ : Δ ⇉ Γ)
    -----------------------------------
    → Γ     ⊢ t₁          ~ t₂          ∶ A 
    → Δ , Γ ⊢ σ₁          ~ σ₂ 
    -----------------------------------
    → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A

ius prf  _       _      σ₁ σ₂ sim-zer       simσ = sim-zer
ius prf (suc n) (suc m) σ₁ σ₂ (sim-suc sim) simσ = sim-suc (ius prf n m σ₁ σ₂ sim simσ)

ius prf       _ _ _         _         (sim-var Z)     (simσ-• _ sim)    = sim
ius (¬■, prf) _ _ (σ₁ • u₁) (σ₂ • u₂) (sim-var (S x)) (simσ-• simσ sim) = 
    ius prf (var x) (var x) σ₁ σ₂ (sim-var x) simσ

ius prf (l₁ ∙ r₁) (l₂ ∙ r₂) σ₁ σ₂ (sim-app simₗ simᵣ) simσ with sit′ simₗ | sit′ simᵣ
... | refl | refl = sim-app (ius prf l₁ l₂ σ₁ σ₂ simₗ simσ) 
                            (ius prf  r₁ r₂ σ₁ σ₂ simᵣ simσ) 

ius prf (ƛ t₁) (ƛ t₂) σ₁ σ₂ (sim-lam sim) simσ with sit′ sim
... | refl = sim-lam (ius (¬■, prf) t₁ t₂ (σ+ σ₁) (σ+ σ₂) sim (lemma-σ+ simσ))

ius prf (unbox t₁) (unbox t₂) σ₁ σ₂ (sim-unbox {ext = ext}) simσ = ⊥-elim (¬■-■ prf ext)

ius prf t₁ t₂ σ₁ σ₂ sim-box _ = sim-box

ius prf (⟨ l₁ , r₁ ⟩) (⟨ l₂ , r₂ ⟩) σ₁ σ₂ (sim-mul sim sim₁) simσ 
    = sim-mul (ius prf l₁ l₂ σ₁ σ₂ sim simσ) (ius prf r₁ r₂ σ₁ σ₂ sim₁ simσ)

ius prf (π₁ t₁) (π₁ t₂) σ₁ σ₂ (sim-pi1 sim) simσ with sit′ sim
... | refl = sim-pi1 (ius prf t₁ t₂ σ₁ σ₂ sim simσ)
ius prf (π₂ t₁) (π₂ t₂) σ₁ σ₂ (sim-pi2 sim) simσ with sit′ sim
... | refl = sim-pi2 (ius prf t₁ t₂ σ₁ σ₂ sim simσ)

ius prf (inl t₁) (inl t₂) σ₁ σ₂ (sim-inl sim) simσ = sim-inl (ius prf t₁ t₂ σ₁ σ₂ sim simσ)
ius prf (inr t₁) (inr t₂) σ₁ σ₂ (sim-inr sim) simσ = sim-inr (ius prf t₁ t₂ σ₁ σ₂ sim simσ)

ius prf (case t₁ of l₁ , r₁) (case t₂ of l₂ , r₂) σ₁ σ₂ (sim-cof sim simₗ simᵣ) simσ 
    = sim-cof (ius prf t₁ t₂ σ₁ σ₂ sim simσ) 
              (ius (¬■, prf) l₁ l₂ (σ+ σ₁) (σ+ σ₂) simₗ (lemma-σ+ simσ))
              (ius (¬■, prf) r₁ r₂ (σ+ σ₁) (σ+ σ₂) simᵣ (lemma-σ+ simσ))

ius prf (fold B t₁)   (fold B t₂)   σ₁ σ₂ (sim-fold sim) simσ   = sim-fold (ius prf t₁ t₂ σ₁ σ₂ sim simσ) 
ius prf (unfold _ refl t₁) (unfold _ refl t₂) σ₁ σ₂ (sim-unfold _ refl sim) simσ = sim-unfold _ refl (ius prf _ _ σ₁ σ₂ sim simσ) 

-- Non-interference for the Fitch calculus
bisim : (t₁ t₂ : Γ ⊢ A)
   → ¬■ Γ → pure A
   → Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ ↝ t₁′ 
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ ↝ t₂′) ×′ (Γ ⊢ t₁′ ~ t₂′ ∶ A))
bisim _ _ ()  p sim-unbox β■
bisim _ _ prf p sim (ξunbox {ext = ext} step) = ⊥-elim (¬■-■ prf ext)

bisim ((ƛ t₁) ∙ r₁) ((ƛ t₂) ∙ r₂) prf p (sim-app (sim-lam simₗ) simᵣ) βƛ 
    with sit′ simₗ | sit′ simᵣ 
... | refl | refl = t₂ [ r₂ ] 
                  ، βƛ 
                  ، ius (¬■, prf) t₁ t₂ (Subst.id • r₁) (Subst.id • r₂) 
                        simₗ 
                        (simσ-• simσ-refl simᵣ)

bisim (l₁ ∙ r₁) (l₂ ∙ r₂) prf p sim@(sim-app simₗ simᵣ) (ξappl step)
                         with  sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl with bisim _ _ prf (p⇒ p) simₗ step
... | l₂′ ، step ، sim′ = l₂′ ∙ r₂ ، ξappl step ، sim-app sim′ simᵣ
 
bisim _ _ prf p (sim-suc sim) (ξsucc step) 
           with sit′ sim 
... | refl with bisim _ _ prf p sim step
... | t₂′ ، step′ ، sim′ = suc t₂′ ، ξsucc step′ ، sim-suc sim′

bisim (case inl t₁ of l₁ , r₁) (case inl t₂ of l₂ , r₂) prf p (sim-cof (sim-inl sim) simₗ simᵣ) βinl 
            with sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl = l₂ [ t₂ ] ، βinl ، ius (¬■, prf) l₁ l₂ (id • t₁) (id • t₂) simₗ (simσ-• simσ-refl sim)

bisim (case inr t₁ of l₁ , r₁) (case inr t₂ of l₂ , r₂) prf p (sim-cof (sim-inr sim) simₗ simᵣ) βinr 
            with sit′ sim | sit′ simₗ | sit′ simᵣ 
... | refl | refl | refl = r₂ [ t₂ ] ، βinr ، ius (¬■, prf) r₁ r₂ (id • t₁) (id • t₂) simᵣ (simσ-• simσ-refl sim)

bisim (π₁ ⟨ l₁ , r₁ ⟩) (π₁ ⟨ l₂ , r₂ ⟩) prf p (sim-pi1 (sim-mul simₗ simᵣ)) βπ₁
    = l₂ ، βπ₁ ، simₗ
bisim (π₂ ⟨ l₁ , r₁ ⟩) (π₂ ⟨ l₂ , r₂ ⟩) prf p (sim-pi2 (sim-mul simₗ simᵣ)) βπ₂
    = r₂ ، βπ₂ ، simᵣ

bisim  (case t₁ of l₁ , r₁) (case t₂ of l₂ , r₂) prf p (sim-cof sim sim₁ sim₂) (ξcase step) 
           with bisim t₁ t₂ prf p+ sim step 
... | t₂′ ، step′ ، sim′ = case t₂′ of l₂ , r₂ ، ξcase step′ ، sim-cof sim′ sim₁ sim₂
bisim  (π₁ t₁) (π₁ t₂) prf p (sim-pi1 sim) (ξπ₁ step) 
           with sit′ sim
... | refl with bisim t₁ t₂ prf p× sim step 
... | t₂′ ، step′ ، sim′ = π₁ t₂′ ، ξπ₁ step′ ، sim-pi1 sim′

bisim (π₂ t₁) (π₂ t₂) prf p (sim-pi2 sim) (ξπ₂ step) 
           with sit′ sim
... | refl with bisim t₁ t₂ prf p× sim step 
... | t₂′ ، step′ ، sim′ = π₂ t₂′ ، ξπ₂ step′ ، sim-pi2 sim′

bisim (unfold B .refl (fold B t₁)) (unfold B .refl (fold B t₂)) prf p (sim-unfold B .refl (sim-fold sim)) βunfold 
    = t₂ ، βunfold ، sim

bisim (unfold B q₁ t₁) (unfold B q₂ t₂) prf p (sim-unfold B q₃ sim) (ξunfold step q₄) with bisim t₁ t₂ prf pμ sim step 
... | t₂′ ، step′ ، sim′ = unfold B q₁ t₂′ ، ξunfold step′ q₁ ، sim-unfold _ q₁ sim′

-- Multi-step bisimulation
bisim⋆ : ¬■ Γ → pure A
       → Γ ⊢ t₁ ~ t₂ ∶ A 
       → t₁ ↝⋆ t₁′ 
       ------------------------------------------------------
       → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ ↝⋆ t₂′) ×′ (Γ ⊢ t₁′ ~ t₂′ ∶ A))
bisim⋆ {t₂ = t₂} prf p sim ⋆refl = t₂ ، ⋆refl ، sim
bisim⋆ prf p sim (⋆step step)       with bisim _ _ prf p  sim step
... | p′ ، sim′ ، step′    = p′ ، ⋆step sim′ ، step′
bisim⋆ prf p sim (⋆trns steps step) with bisim⋆ prf p sim steps 
... | t₂′ ، steps′ ، sim′        with bisim _ _ prf p sim′ step
... | t₂′′ ، step′ ، sim′′ = t₂′′ ، ⋆trns steps′ step′ ، sim′′


non-interference : (v : ∅        ⊢ Nat)
                 → (V : ∅ , □ A  ⊢ Nat) 
                 → (t : ∅        ⊢ □ A)
                 → (u : ∅        ⊢ □ A)
                 → V [ t ] ⇓ v
                 -------------
                 → V [ u ] ⇓ v
non-interference v V t u V[t]-reduces = 
    let stepsₗ ، v-value             = V[t]-reduces
        t~u                          = sim-box
        V~V                          = sim-refl V
        V[t]~V[u]                    = ius (¬■, ¬■∅) V V (id • t) (id • u) V~V (simσ-• simσ-ε t~u)
        V[u]′ ، stepsᵣ ، v~V[u]′      = bisim⋆ ¬■∅ pℕ V[t]~V[u] stepsₗ
        V[u]′-value                  = sim-value v V[u]′ v~V[u]′ v-value
        v≡V[u]′                      = ind-eql v V[u]′ v-value V[u]′-value v~V[u]′
         
        V[u]↝⋆v                     = subst (λ p → V [ u ] ↝⋆ p) (sym v≡V[u]′) stepsᵣ
    in V[u]↝⋆v ، proj₂ V[t]-reduces     
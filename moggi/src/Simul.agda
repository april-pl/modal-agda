module Simul where
open import Base
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _⸲_)
open import Subst

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ l l′ r r′ : _ ⊢ _
    A B C : Type
    Γ Γ′ Δ Δ₁ Δ₂ Γ₁ Γ₂ θ : Context
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    sim-one : Γ ⊢ ⋆ ~ ⋆ ∶ Unit

    sim-mon : (t  : Γ ⊢ T A)  
            → (t′ : Γ ⊢ T A)
            ----------------
            → Γ ⊢ t ~ t′ ∶ T A

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

    sim-mul : Γ ⊢ l         ~          l′ ∶ A
            → Γ ⊢ r         ~          r′ ∶ B
            -------------------------------------
            → Γ ⊢ ⟨ l , r ⟩ ~ ⟨ l′ , r′ ⟩ ∶ A × B

    sim-pi1 : Γ ⊢ t    ~ t′    ∶ A × B
            --------------------------
            → Γ ⊢ π₁ t ~ π₁ t′ ∶ A

    sim-pi2 : Γ ⊢ t    ~ t′    ∶ A × B
            --------------------------
            → Γ ⊢ π₂ t ~ π₂ t′ ∶ B

    sim-cof : Γ     ⊢ t               ~ t′                 ∶ A + B
            → Γ , A ⊢ l               ~ l′                 ∶ C
            → Γ , B ⊢ r               ~ r′                 ∶ C
            --------------------------------------------------
            → Γ     ⊢ case t of l , r ~ case t′ of l′ , r′ ∶ C
    
    sim-inl : Γ ⊢ t     ~ t′     ∶ A
            ------------------------------------
            → Γ ⊢ inl {B = B} t ~ inl {B = B} t′ ∶ A + B
        
    sim-inr : Γ ⊢ t     ~ t′     ∶ B
            ------------------------------------
            → Γ ⊢ inr {A = A} t ~ inr {A = A} t′ ∶ A + B

    sim-fold : {B : TypeIn (new none)}
             → {t t′ : Γ ⊢ B ⁅ Rec B ⁆}
             → Γ ⊢ t ~ t′ ∶ B ⁅ Rec B ⁆
             --------------------------
             → Γ ⊢ fold B t ~ fold B t′ ∶ Rec B

    sim-unfold : (B : TypeIn (new none))
               → {t t′ : Γ ⊢ Rec B}
               → (p : C ≡ B ⁅ Rec B ⁆)
               → Γ ⊢ t ~ t′ ∶ Rec B
               --------------------
               → Γ ⊢ unfold B p t ~ unfold B p t′ ∶ C

sim-refl : (t : Γ ⊢ A) → Γ ⊢ t ~ t ∶ A
sim-refl ⋆             = sim-one
sim-refl (var x)       = sim-var x
sim-refl (η t)         = sim-mon (η t) (η t)
sim-refl (ƛ t)         = sim-lam (sim-refl t)
sim-refl (l ∙ r)       = sim-app (sim-refl l) (sim-refl r)
sim-refl (bind t of u) = sim-mon _ _
sim-refl (inl t)       = sim-inl (sim-refl t)
sim-refl (inr t)       = sim-inr (sim-refl t)
sim-refl (case t of l , r) = sim-cof (sim-refl t) (sim-refl l) (sim-refl r)
sim-refl (π₁ t)        = sim-pi1 (sim-refl t)
sim-refl (π₂ t)        = sim-pi2 (sim-refl t)
sim-refl ⟨ l , r ⟩     = sim-mul (sim-refl l) (sim-refl r)
sim-refl (fold A t)    = sim-fold (sim-refl t)
sim-refl (unfold A p t)  = sim-unfold _ p (sim-refl t)

sit : (t₁ t₂ : Γ ⊢ B) → Γ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit _ _ sim-one          = refl
sit _ _ (sim-mon _ _)    = refl
sit _ _ (sim-var x)      = refl
sit _ _ (sim-fold sim)   = refl
sit _ _ (sim-unfold _ _ sim) = refl
sit _ _ (sim-lam sim)           with sit _ _ sim 
... | refl = refl
sit _ _ (sim-app simₗ simᵣ)     with sit _ _ simₗ
... | refl = refl
sit _ _ (sim-inl sim)           with sit _ _ sim 
... | refl = refl
sit _ _ (sim-inr sim)           with sit _ _ sim 
... | refl = refl 
sit _ _ (sim-cof sim simₗ simᵣ) with sit _ _ sim | sit _ _ simₗ | sit _ _ simᵣ
... | refl | refl | refl = refl
sit _ _ (sim-pi1 sim) with sit _ _ sim 
... | refl = refl
sit _ _ (sim-pi2 sim) with sit _ _ sim 
... | refl = refl
sit _ _ (sim-mul simₗ simᵣ) with sit _ _ simₗ | sit _ _ simᵣ  
... | refl | refl = refl 

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
 
simσ-refl : Δ , Γ ⊢ σ ~ σ
simσ-refl {σ = ε}         = simσ-ε
simσ-refl {σ = σ • t}     = simσ-• simσ-refl (sim-refl t)

-- Lemmas regarding simulation 
module Lemmas where
    -- Weakening is respectful
    sim-weak : (t₁ t₂ : Γ ⊢ A) 
             → (wk : Γ ⊆ Δ) 
             → Γ ⊢ t₁ ~ t₂ ∶ A 
             → Δ ⊢ weakening wk t₁ ~ weakening wk t₂ ∶ A
    sim-weak ⋆ ⋆ wk sim-one = sim-one
    
    sim-weak t₁ t₂ wk (sim-mon _ _) = sim-mon (weakening wk t₁) (weakening wk t₂)
    sim-weak _  _  wk (sim-var x)   = sim-var (Γ-weak wk x)

    sim-weak (l₁ ∙ r₁)  (l₂ ∙ r₂) wk (sim-app simₗ simᵣ) with sit′ simₗ | sit′ simᵣ
    ... | refl | refl = sim-app (sim-weak l₁ l₂ wk simₗ) 
                                (sim-weak r₁ r₂ wk simᵣ)

    sim-weak (ƛ t₁) (ƛ t₂) wk (sim-lam sim) = sim-lam (sim-weak t₁ t₂ (⊆-keep wk) sim)

    sim-weak (⟨ l₁ , r₁ ⟩) (⟨ l₂ , r₂ ⟩) wk (sim-mul sim sim₁) 
        = sim-mul (sim-weak l₁ l₂ wk sim) (sim-weak r₁ r₂ wk sim₁)
        
    sim-weak (π₁ t₁) (π₁ t₂) wk (sim-pi1 sim) with sit′ sim
    ... | refl = sim-pi1 (sim-weak t₁ t₂ wk sim)
    sim-weak (π₂ t₁) (π₂ t₂) wk (sim-pi2 sim) with sit′ sim
    ... | refl = sim-pi2 (sim-weak t₁ t₂ wk sim)

    sim-weak (case t₁ of l₁ , r₁) (case t₂ of l₂ , r₂) wk (sim-cof sim sim₁ sim₂) 
        = sim-cof (sim-weak t₁ t₂ wk sim) (sim-weak l₁ l₂ (⊆-keep wk) sim₁) (sim-weak r₁ r₂ (⊆-keep wk) sim₂)
    
    sim-weak (inl t₁) (inl t₂) wk (sim-inl sim) = sim-inl (sim-weak t₁ t₂ wk sim)
    sim-weak (inr t₁) (inr t₂) wk (sim-inr sim) = sim-inr (sim-weak t₁ t₂ wk sim)

    sim-weak (fold _ t₁)   (fold _ t₂)   wk (sim-fold sim)   = sim-fold (sim-weak t₁ t₂ wk sim)
    sim-weak (unfold _ _ t₁) (unfold _ _ t₂) wk (sim-unfold _ _ sim) = sim-unfold _ _ (sim-weak t₁ t₂ wk sim)          

    -- w/ implicit arguments
    sim-weak′ : {t₁ t₂ : Γ ⊢ A} 
              → {wk : Γ ⊆ Δ}
              → Γ ⊢ t₁ ~ t₂ ∶ A 
              → Δ ⊢ weakening wk t₁ ~ weakening wk t₂ ∶ A
    sim-weak′ {t₁} {t₂} {wk} sim = sim-weak t₁ t₂ wk sim

    -- Context weakening is respectful
    lemma-wk : Δ       , Γ       ⊢ σ₁     ~ σ₂
             → (Δ , A) , Γ       ⊢ wk σ₁  ~ wk σ₂
    lemma-wk simσ-ε          = simσ-ε
    lemma-wk (simσ-• simσ x) = simσ-• (lemma-wk simσ) (sim-weak′ x) 

    -- As above 
    lemma-σ+ : Γ       , Δ       ⊢ σ            ~ τ
         → (Γ , A) , (Δ , A) ⊢ σ+ {A = A} σ ~ σ+ {A = A} τ
    lemma-σ+ simσ-ε         = simσ-• simσ-ε (sim-var Z) 
    lemma-σ+ (simσ-• sim x) = 
        simσ-• (simσ-• (lemma-wk sim) (sim-weak′ x)) 
               (sim-var Z) 
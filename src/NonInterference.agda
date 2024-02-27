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
open import Data.Product renaming (_,_ to _،_)
open import Subst
open import Simul

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Δ Δ′ Γ₁ Γ₂ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _ 

-- lemma-st : (w : Δ′ ⊆ Δ) 
--             → Γ , Δ  ⊢ σ ~ τ 
--             ---------------------------------------
--             → Γ , Δ′ ⊢ ⇉-st σ w ~ ⇉-st τ w
-- lemma-st ⊆-empty simσ-ε = simσ-ε
-- --------------------------------
-- lemma-st ⊆-empty (simσ-p w₁) = simσ-ε
-- lemma-st (⊆-drop w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-drop w) w₁)
-- lemma-st (⊆-keep w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-keep w) w₁)
-- lemma-st (⊆-lock w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-lock w) w₁)
-- ----------------------------------------------------------------
-- lemma-st (⊆-lock w) (simσ-■ simσ) = simσ-■ (lemma-st w simσ)
-- ------------------------------------------------------------
-- lemma-st (⊆-drop w) (simσ-• simσ x) = lemma-st w simσ
-- lemma-st (⊆-keep w) (simσ-• simσ x) = simσ-• (lemma-st w simσ) x

-- {-# TERMINATING #-}
-- mutual 
--     lemma-σ+ : ¬■ Γ
--              → ¬■ Δ
--              → Γ       , Δ       ⊢ σ            ~ τ
--              → (Γ , A) , (Δ , A) ⊢ σ+ {A = A} σ ~ σ+ {A = A} τ

--     ius : ¬■ Γ
--         → ¬■ Δ
--         → (t₁ t₂ : Γ ⊢ A)
--         → (σ₁ σ₂ : Δ ⇉ Γ)
--         -----------------------------------
--         → Γ     ⊢ t₁          ~ t₂          ∶ A 
--         → Δ , Γ ⊢ σ₁          ~ σ₂ 
--         -----------------------------------
--         → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A

--     lemma-σ+ prf₁ prf₂ simσ-ε     = simσ-• simσ-ε                                (sim-var Z)
--     lemma-σ+ prf₁ prf₂ (simσ-p w) = simσ-• (lemma-st w (simσ-p (⊆-drop ⊆-refl))) (sim-var Z)
--     lemma-σ+ prf₁ (¬■, prf₂) (simσ-• {σ = σ} {t₁ = t₁} {t₂ = t₂} simσ simₜ) with lemma-σ+ prf₁ prf₂ simσ
--     ... | simσ-• simσ′ r = simσ-• (simσ-• simσ′ (ius prf₁ (¬■, prf₁) t₁ t₂ p p simₜ simσ-refl)) r


    -- -- The indistinguishability under substitution lemma.
    -- ius _ _ t₁ t₂ σ τ (sim-nat n)        simσ = sim-nat n
    -- -------------------------------------------------
    -- ius _ _ t₁ t₂ σ τ (sim-lock ext _ _) simσ = sim-lock (is∷-Δsub ext σ) (sub σ t₁) (sub τ t₂)
    -- ---------------------------------------------------------------------------------------
    -- ius prf₁       prf₂       t₁ t₂ (wk w) (wk w) (sim-var Z)     (simσ-p w) = sim-var (Γ-weak w Z)
    -- ius (¬■, prf₁) prf₂ t₁ t₂ (wk w) (wk w) (sim-var (S x)) (simσ-p w) =
    --     let w′ = ⊆-assoc (⊆-drop ⊆-refl) w
    --     in ius prf₁ prf₂ (var x) (var x) (wk w′) (wk w′) (sim-var x) (simσ-p w′)
    -- -----------------------------------------------------------------
    -- ius prf₁       prf₂ t₁ t₂ (σ • _) (τ • _) (sim-var Z)     (simσ-• simσ simᵤ) = simᵤ
    -- ius (¬■, prf₁) prf₂ t₁ t₂ (σ • _) (τ • _) (sim-var (S x)) (simσ-• simσ simᵤ) =
    --     ius prf₁ prf₂ (var x) (var x) (⇉-st σ ⊆-refl) (⇉-st τ ⊆-refl) (sim-var x) (lemma-st ⊆-refl simσ)
    -- -----------------------------------------------------------------------------------
    -- ius prf₁ prf₂ (l₁ ∙ r₁) (l₂ ∙ r₂) σ τ (sim-app simₗ simᵣ) simσ with sit _ _ simₗ | sit _ _ simᵣ
    -- ... | refl | refl = sim-app (ius prf₁ prf₂ l₁ l₂ σ τ simₗ simσ) (ius prf₁ prf₂ r₁ r₂ σ τ simᵣ simσ)
    -- -------------------------------------------------------------------------------
    -- ius prf₁ prf₂ (ƛ b₁) (ƛ b₂) σ τ (sim-lam simₜ) simσ with sit b₁ b₂ simₜ
    -- ... | refl = sim-lam (ius (¬■, prf₁) (¬■, prf₂) b₁ b₂ (σ+ σ) (σ+ τ) simₜ (lemma-σ+ prf₂ prf₁ simσ))
    -- ---------------------------------------------------------------------------------
    -- ius prf₁ prf₂ (box b₁) (box b₂) σ τ (sim-box simₜ) simσ with sit b₁ b₂ simₜ
    -- ... | refl = sim-box (sim-lock is-nil (sub (σ •■) b₁) (sub (τ •■) b₂))

-- -- Non-interference for the Fitch calculus
-- ni : ¬■ Γ
--    → Γ ⊢ t₁ ~ t₂ ∶ A 
--    → t₁ →β t₁′ 
--    ------------------------------------------------------
--    → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
-- ni prf (sim-lock ext _ _) _ = ⊥-elim (¬■-■ prf ext)
-- ni ()  (sim-unbox _)      _
-- ---------------------------------------------------

-- ni prf sim@(sim-app {t₁ = f₁} {f₂} {t₂ = x₁} {x₂} simƛ simᵣ) βƛ 
--                                  with sit _ _ sim | sit _ _ simƛ | sit _ _ simᵣ 
-- ... | refl | refl | refl         with simƛ 
-- ... | sim-lock ext _ _ = ⊥-elim (¬■-■ prf ext)
-- ... | sim-lam {t = b₁} {b₂} sim∘ with sit _ _ sim∘
-- ... | refl = b₂ [ x₂ ] 
--            ، βƛ 
--            ، ius (¬■, prf) prf b₁ b₂ (sub-refl • x₁) (sub-refl • x₂) sim∘ (simσ-• simσ-refl simᵣ)

-- ni prf sim@(sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappl step) 
--                          with sit _ _ sim | sit _ _ simₗ | sit _ _ simᵣ 
-- ... | refl | refl | refl with ni prf simₗ step
-- ... | l₂′ ، βl₂ ، ind    with sit _ _ ind
-- ... | refl = l₂′ ∙ r₂ 
--            ، ξappl βl₂ 
--            ، sim-app ind simᵣ

-- ni prf sim@(sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappr step) 
--                          with sit _ _ sim | sit _ _ simₗ | sit _ _ simᵣ 
-- ... | refl | refl | refl with ni prf simᵣ step
-- ... | r₂′ ، βr₂ ، ind    with sit _ _ ind
-- ... | refl = l₂ ∙ r₂′ 
--            ، ξappr βr₂ 
--            ، sim-app simₗ ind
           
               
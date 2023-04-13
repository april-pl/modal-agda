{-# OPTIONS --allow-unsolved-metas #-}
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
    lemma-st (⊆-lock w) (simσ-p w₁) = simσ-p (⊆-assoc (⊆-lock w) w₁)
    ----------------------------------------------------------------
    lemma-st (⊆-lock w) (simσ-■ simσ) = simσ-■ (lemma-st w simσ)
    ------------------------------------------------------------
    lemma-st (⊆-drop w) (simσ-• simσ x) = lemma-st w simσ
    lemma-st (⊆-keep w) (simσ-• simσ x) = simσ-• (lemma-st w simσ) x

    lemma-σ+ : ¬■ Δ
             → Γ       , Δ       ⊢ σ            ~ τ
             → (Γ , A) , (Δ , A) ⊢ σ+ {A = A} σ ~ σ+ {A = A} τ
    lemma-σ+ prf simσ-ε     = simσ-• simσ-ε                                (sim-var Z)
    lemma-σ+ prf (simσ-p w) = simσ-• (lemma-st w (simσ-p (⊆-drop ⊆-refl))) (sim-var Z)
    lemma-σ+ (¬■, prf) (simσ-• simσ simₜ) with lemma-σ+ prf simσ
    ... | simσ-• simσ′ r = simσ-• (simσ-• simσ′ {!   !}) r

open lemmas

ius : ¬■ Γ
    → (t₁ t₂ : Γ ⊢ A)
    → (σ₁ σ₂ : Δ ⇉ Γ)
    -----------------------------------
    → Γ     ⊢ t₁          ~ t₂          ∶ A 
    → Δ , Γ ⊢ σ₁          ~ σ₂ 
    -----------------------------------
    → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A
-- The indistinguishability under substitution lemma.
ius prf t₁ t₂ σ τ (sim-nat n)        simσ = sim-nat n
-------------------------------------------------
ius prf t₁ t₂ σ τ (sim-lock ext _ _) simσ = sim-lock (is∷-Δsub ext σ) (sub σ t₁) (sub τ t₂)
---------------------------------------------------------------------------------------
ius prf       t₁ t₂ (wk w) (wk w) (sim-var Z)     (simσ-p w) = sim-var (Γ-weak w Z)
ius (¬■, prf) t₁ t₂ (wk w) (wk w) (sim-var (S x)) (simσ-p w) =
    let w′ = ⊆-assoc (⊆-drop ⊆-refl) w
    in ius prf (var x) (var x) (wk w′) (wk w′) (sim-var x) (simσ-p w′)
-----------------------------------------------------------------
ius prf       t₁ t₂ (σ • _) (τ • _) (sim-var Z)     (simσ-• simσ simᵤ) = simᵤ
ius (¬■, prf) t₁ t₂ (σ • _) (τ • _) (sim-var (S x)) (simσ-• simσ simᵤ) =
    ius prf (var x) (var x) (⇉-st σ ⊆-refl) (⇉-st τ ⊆-refl) (sim-var x) (lemma-st ⊆-refl simσ)
-----------------------------------------------------------------------------------
ius prf (l₁ ∙ r₁) (l₂ ∙ r₂) σ τ (sim-app simₗ simᵣ) simσ with sit _ _ simₗ | sit _ _ simᵣ
... | refl | refl = sim-app (ius prf l₁ l₂ σ τ simₗ simσ) (ius prf r₁ r₂ σ τ simᵣ simσ)
-------------------------------------------------------------------------------
ius prf (ƛ b₁) (ƛ b₂) σ τ (sim-lam simₜ) simσ    with sit b₁ b₂ simₜ
... | refl = sim-lam (ius (¬■, prf) b₁ b₂ (σ+ σ) (σ+ τ) simₜ (lemma-σ+ prf simσ))
-- ius prf (ƛ b₁) (ƛ b₂) ε ε (sim-lam simₜ) simσ-ε    with sit b₁ b₂ simₜ 
-- ... | refl = let σ′ = ε • var Z
--                  τ′ = ε • var Z
--              in sim-lam (ius (¬■, prf) b₁ b₂ σ′ τ′ simₜ (simσ-• simσ-ε (sim-var Z)))
                
-- ius prf (ƛ b₁) (ƛ b₂) _ _ (sim-lam simₜ) (simσ-p w) with sit b₁ b₂ simₜ
-- ... | refl = let σ′ = ⇉-st p w • var Z
--                  τ′ = ⇉-st p w • var Z
--              in sim-lam (ius (¬■, prf) b₁ b₂ σ′ τ′ simₜ (simσ-• 
--                     (lemma-st w (simσ-p (⊆-drop ⊆-refl))) (sim-var Z)))

-- ius prf (ƛ b₁) (ƛ b₂) (σ • t) (τ • u) (sim-lam simₜ) (simσ-• simσ x) with sit b₁ b₂ simₜ 
-- ... | refl = let σ′   = ((σ ◦ p) • sub p t) • var Z
--                  τ′   = ((τ ◦ p) • sub p u) • var Z
--                  sim+ = simσ-• {!   !} {!   !} 
--              in sim-lam (ius (¬■, prf) b₁ b₂ σ′ τ′ simₜ (simσ-• sim+ (sim-var Z)))
            --  in sim-lam (ius (¬■, prf) b₁ b₂ σ′ τ′ simₜ {!   !})
                    -- (simσ-• (simσ-• {!   !} 
                    --                 (ius {!   !} t u p p x (simσ-p (⊆-drop ⊆-refl)))
                    --             ) (sim-var Z)))
-- with sit b₁ b₂ simₜ 
-- ... | refl = let σ′ = (σ ◦ wk (⊆-drop ⊆-refl)) • var Z
--                  τ′ = (τ ◦ wk (⊆-drop ⊆-refl)) • var Z
--     in sim-lam (ius (¬■, prf) b₁ b₂ σ′ τ′ simₜ (simσ-• {!   !} (sim-var Z)))
----------------------------------------------------
ius prf (box b₁) (box b₂) σ τ (sim-box simₜ) simσ with sit b₁ b₂ simₜ
... | refl = sim-box (sim-lock is-nil (sub (σ •■) b₁) (sub (τ •■) b₂))

    
--------------------------------------------------------
-- ius prf (unbox b₁) (unbox b₂) σ τ (sim-unbox simₜ) simσ with sit b₁ b₂ simₜ 
-- ... | refl = ⊥-elim (¬■LF prf)

-- ius _ t₁ t₂ a₁ a₂ (sim-lock (is-ext ext) _ _) sim₂ = sim-lock ext (t₁ [ a₁ ]) (t₂ [ a₂ ])
-- ---------------------------------------------------------------------------------------
-- ius _ t₁ t₂ a₁ a₂ (sim-var Z)     sim₂ = sim₂
-- ius _ t₁ t₂ a₁ a₂ (sim-var (S x)) sim₂ rewrite sub-refl-id-var (var x) refl with is∷-∈ x  
-- ... | Γ₁ ، Γ₂ ، ext = sim-var x
-- --------------------------------------------
-- ius prf t₁ t₂ a₁ a₂ (sim-app  {t₁ = l₁} {t₁′ = l₂} {A = T} {B = U} {t₂ = r₁} {t₂′ = r₂} simₗ simᵣ) sim₂ with sit l₁ l₂ simₗ | sit r₁ r₂ simᵣ
-- ... | refl | refl = sim-app (ius prf l₁ l₂ a₁ a₂ simₗ sim₂) (ius prf r₁ r₂ a₁ a₂ simᵣ sim₂)
-- -----------------------------------------------------------------------------------
-- ius prf t₁ t₂ a₁ a₂ sim@(sim-lam {A = T} {t = b₁} {t′ = b₂} {B = U} sim₁) sim₂ 
--     with sit _ _ sim | sit b₁ b₂ sim₁ | sit _ _ sim₂
-- ... | refl | refl | refl = 
--     let a = {!   !}
--     --in sim-lam (ius (¬■, prf) {!  !} {!   !} {!   !} {!   !} {!   !} {!  !})
--     in {!   !}
-- ---------------------------------------------------
-- ius _ t₁ t₂ a₁ a₂ (sim-box {t = b₁} {t′ = b₂} sim₁) sim₂ with sit b₁ b₂ sim₁
-- ... | refl = sim-box (sim-lock is-nil (sub (sub-lock (sub-subs sub-refl a₁)) b₁)
--                                       (sub (sub-lock (sub-subs sub-refl a₂)) b₂))


-- Non-interference for the Fitch calculus
ni : ¬■ Γ
   → Γ ⊢ t₁ ~ t₂ ∶ A 
   → t₁ →β t₁′ 
   ------------------------------------------------------
   → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
ni prf (sim-lock ext _ _) _ = ⊥-elim (¬■-■ prf ext)
ni ()  (sim-unbox _)      _
---------------------------------------------------

ni prf sim@(sim-app {t₁ = f₁} {f₂} {t₂ = x₁} {x₂} simƛ simᵣ) βƛ 
                                 with sit _ _ sim | sit _ _ simƛ | sit _ _ simᵣ 
... | refl | refl | refl         with simƛ 
... | sim-lock ext _ _ = ⊥-elim (¬■-■ prf ext)
... | sim-lam {t = b₁} {b₂} sim∘ with sit _ _ sim∘
... | refl = b₂ [ x₂ ] 
           ، βƛ 
           ، ius (¬■, prf) b₁ b₂ (sub-refl • x₁) (sub-refl • x₂) sim∘ (simσ-• simσ-refl simᵣ)
        --    ، ius prf b₁ b₂ x₁ x₂ sim∘ simᵣ
            -- ، ius b₁ b₂ {! sub-subs ? ? !} sim∘

ni prf sim@(sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappl step) 
                         with sit _ _ sim | sit _ _ simₗ | sit _ _ simᵣ 
... | refl | refl | refl with ni prf simₗ step
... | l₂′ ، βl₂ ، ind    with sit _ _ ind
... | refl = l₂′ ∙ r₂ 
           ، ξappl βl₂ 
           ، sim-app ind simᵣ

ni prf sim@(sim-app {t₁ = l₁} {l₂} {t₂ = r₁} {r₂} simₗ simᵣ) (ξappr step) 
                         with sit _ _ sim | sit _ _ simₗ | sit _ _ simᵣ 
... | refl | refl | refl with ni prf simᵣ step
... | r₂′ ، βr₂ ، ind    with sit _ _ ind
... | refl = l₂ ∙ r₂′ 
           ، ξappr βr₂ 
           ، sim-app simₗ ind
           
              
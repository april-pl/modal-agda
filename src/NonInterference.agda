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
    Γ Δ Γ₁ Γ₂ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂
    σ σ′ σ₁ σ₂ τ τ′ : _ ⇉ _

private lemma-st : Γ , Δ ⊢ σ ~ τ 
                 ---------------------------------------
                 → Γ , Δ ⊢ ⇉-st σ ⊆-refl ~ ⇉-st τ ⊆-refl
lemma-st simσ-ε              = simσ-ε
lemma-st (simσ-p ⊆-empty)    = simσ-ε
lemma-st (simσ-■ simσ)       = simσ-■ (lemma-st simσ)
lemma-st (simσ-• simσ x)     = simσ-• (lemma-st simσ) x
-----------------------------------------------------------------
lemma-st (simσ-p (⊆-keep w)) = simσ-p (⊆-keep (⊆-assoc ⊆-refl w))
lemma-st             (simσ-p (⊆-lock w)) = simσ-p (⊆-lock (⊆-assoc ⊆-refl w))
lemma-st {Δ = ∅}     (simσ-p (⊆-drop w)) = simσ-ε
lemma-st {Δ = Δ ■}   (simσ-p (⊆-drop w)) = simσ-p (⊆-drop (⊆-assoc (⊆-lock ⊆-refl) w))
lemma-st {Δ = Δ , x} (simσ-p (⊆-drop w)) = simσ-p (⊆-drop (⊆-assoc (⊆-keep ⊆-refl) w))


-- The indistinguishability under substitution lemma.
ius : (t₁ t₂ : Γ ⊢ A)
    → (σ₁ σ₂ : Δ ⇉ Γ)
    -----------------------------------
    → Γ     ⊢ t₁          ~ t₂          ∶ A 
    → Δ , Γ ⊢ σ₁          ~ σ₂ 
    -----------------------------------
    → Δ     ⊢ (sub σ₁ t₁) ~ (sub σ₂ t₂) ∶ A
ius t₁ t₂ σ τ (sim-lock ext _ _) simσ = sim-lock (is∷-Δsub ext σ) (sub σ t₁) (sub τ t₂)
---------------------------------------------------------------------------------------
ius t₁ t₂ (wk w) (wk w) (sim-var Z)     (simσ-p w) = sim-var (Γ-weak w Z)
ius t₁ t₂ (wk w) (wk w) (sim-var (S x)) (simσ-p w) =
    let w′ = ⊆-assoc (⊆-drop ⊆-refl) w
    in ius (var x) (var x)(wk w′) (wk w′) (sim-var x) (simσ-p w′)
-----------------------------------------------------------------
ius t₁ t₂ (σ • _) (τ • _) (sim-var Z)     (simσ-• simσ simᵤ) = simᵤ
ius t₁ t₂ (σ • _) (τ • _) (sim-var (S x)) (simσ-• simσ simᵤ) =
    ius (var x) (var x) (⇉-st σ ⊆-refl) (⇉-st τ ⊆-refl) (sim-var x) (lemma-st simσ)
-----------------------------------------------------------------------------------
ius (l₁ ∙ r₁) (l₂ ∙ r₂) σ τ (sim-app simₗ simᵣ) simσ with sit _ _ simₗ | sit _ _ simᵣ
... | refl | refl = sim-app (ius l₁ l₂ σ τ simₗ simσ) (ius r₁ r₂ σ τ simᵣ simσ)
-------------------------------------------------------------------------------
ius (ƛ b₁) (ƛ b₂) σ τ (sim-lam simₜ) simσ with sit b₁ b₂ simₜ 
... | refl = let σ′ = (σ ◦ wk (⊆-drop ⊆-refl)) • var Z
                 τ′ = (τ ◦ wk (⊆-drop ⊆-refl)) • var Z
    in sim-lam (ius b₁ b₂ σ′ τ′ simₜ {!   !}) -- write lemma sim to st one
----------------------------------------------------
ius (box b₁) (box b₂) σ τ (sim-box simₜ) simσ with sit b₁ b₂ simₜ
... | refl = sim-box (sim-lock is-nil (sub (σ •■) b₁) (sub (τ •■) b₂))
--------------------------------------------------------
ius (unbox b₁) (unbox b₂) σ τ (sim-unbox simₜ) simσ with sit b₁ b₂ simₜ 
... | refl = {! sim-lock  !}

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


-- Obviously this proof will require some lemmas, and here they are.
private module lemmas where
    simσ-◦p : Γ ,       Δ ⊢ σ     ~ τ 
            -----------------------------
            → (Γ , A) , Δ ⊢ σ ◦ p ~ τ ◦ p
            
    simσ-◦p simσ-ε = simσ-ε
    simσ-◦p (simσ-p w) = {!   !}
    simσ-◦p (simσ-■ sim) = {!   !}
    simσ-◦p (simσ-• {t₁ = t₁} {t₂ = t₂} sim simₜ) = simσ-• 
        (simσ-◦p sim) 
        (ius t₁ t₂ (wk (⊆-drop ⊆-refl)) (wk (⊆-drop ⊆-refl)) simₜ (simσ-p (⊆-drop ⊆-refl)))

    simσ-refl : Γ , Γ ⊢ sub-refl ~ sub-refl
    simσ-refl {∅}     = simσ-ε
    simσ-refl {Γ , A} = simσ-• (simσ-◦p simσ-refl) (sim-var Z)
    simσ-refl {Γ ■}   = simσ-■ simσ-refl
        
open lemmas

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
           ، ius b₁ b₂ (sub-refl • x₁) (sub-refl • x₂) sim∘ (simσ-• simσ-refl simᵣ)
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
           
       
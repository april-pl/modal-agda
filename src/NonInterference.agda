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

-- Obviously this proof will require some syntactic lemmas, and here they are.
private module lemmas where
    -- sim-weak : (t₁ t₂ : Γ ⊢ A) → Γ ⊆ Δ → Γ ⊢ t₁ ~ t₂ ∶ A → Σ[ t₁′ ∈ Δ ⊢ A ] Σ[ t₂′ ∈ Δ ⊢ A ] (Δ ⊢ t₁′ ~ t₂′ ∶ A)
    -- sim-weak t₁ t₂ ⊆-empty     sim = t₁ ، t₂ ، sim
    -- sim-weak t₁ t₂ (⊆-drop wk) sim with sim-weak t₁ t₂ wk sim
    -- ... | t₁′ ، t₂′ ، sim′ = {!  !} ، {!   !} ، {!  !}
    -- sim-weak t₁ t₂ (⊆-keep wk) sim = {! !} ، {!   !} ، {!   !}
    -- sim-weak t₁ t₂ (⊆-lock wk) sim = {!   !} ، {!   !} ، {!   !}

    -- ius-sub-keep : Γ , B , A  ⊢ sub           (sub-subs sub-refl a₁)  b₁ ~ sub           (sub-subs sub-refl a₂)  b₂ ∶ B
    --              → Γ , A      ⊢ sub (sub-keep (sub-subs sub-refl a₁)) b₁ ~ sub (sub-keep (sub-subs sub-refl a₂)) b₂ ∶ B
    -- ius-sub-keep = ?

    -- lemma-sub : Γ     ⊢ sub s₁ (ƛ t₁)        
    --           → Γ , A ⊢ sub (sub-keep s₁) t₁ ~ sub (sub-keep s₂) t₂ : B

open lemmas

-- The indistinguishability under substitution lemma.
-- God, this is disgusting, isn't it?
ius : (t₁ t₂ : Γ ⊢ A)
    → (σ : Δ ⇉ Γ)
    -----------------------------------
    → Γ ⊢ t₁         ~ t₂         ∶ A 
    -----------------------------------
    → Δ ⊢ (sub σ t₁) ~ (sub σ t₂) ∶ A
ius = {!   !}
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
        --    ، ius prf b₁ b₂ x₁ x₂ sim∘ simᵣ
            ، {!   !}
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
           

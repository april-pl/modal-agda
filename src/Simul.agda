module Simul where
open import Base
open import LFExt
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.Bool 
open import Data.Product renaming (_,_ to _⸲_)
open import Subst

private variable
    t t′ t₁ t₂ t₁′ t₂′ a a₁ a₂ a′ b b₁ b₂ b′ : _ ⊢ _
    A B : Type
    Γ Δ Γ₁ Γ₂ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Δ ⊢ A → Δ ⊢ A → (A : Type) → Set where
    sim-lock : Γ is Γ₁ ■ ∷ Γ₂
             → (t  : Γ ⊢ A) 
             → (t′ : Γ ⊢ A)
             ------------------
             → Γ ⊢ t ~ t′ ∶ A

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

    sim-box : Γ ■ ⊢ t     ~ t′     ∶ A
            ----------------------------
            → Γ   ⊢ box t ~ box t′ ∶ □ A
    
    sim-unbox : Γ   ⊢ t                    ~ t′                    ∶ □ A
              ----------------------------------------------------------
              → Γ ■ ⊢ unbox {ext = □ext} t ~ unbox {ext = □ext} t′ ∶ A

    sim-weak : Γ ⊢ t ~ t′ ∶ A
             → Γ ⊆ Δ
             ----------------
             → Δ ⊢ t ~ t′ ∶ A


-- Lemma to make sure sim-weak doesn't mess everything up
-- sim-⊆ : {t t′ : Γ ⊢ A} → Δ ⊢ t ~ t′ ∶ A → Γ ⊆ Δ
-- sim-⊆ (sim-lock x _ _) = ⊆-refl
-- sim-⊆ (sim-var x) = ⊆-refl
-- sim-⊆ (sim-app simₗ simᵣ) = sim-⊆ {!   !}
-- sim-⊆ (sim-lam sim) = {!   !}
-- sim-⊆ (sim-box sim) = {!   !}
-- sim-⊆ (sim-unbox sim) = {!   !}
-- sim-⊆ (sim-weak sim x) = {!   !}

-- sim-unweak : {t t′ : Γ ⊢ A} → Δ ⊢ t ~ t′ ∶ A → Γ ⊢ t ~ t′ ∶ A
-- sim-unweak (sim-var x)         = sim-var x
-- sim-unweak (sim-lock ext _ _)  = {! sim-lock x t t′ !}
-- sim-unweak (sim-app simₗ simᵣ) = sim-app {!   !} {!   !}
-- sim-unweak (sim-lam sim)       = sim-lam (sim-unweak sim)
-- sim-unweak (sim-box sim)       = sim-box (sim-unweak sim)
-- sim-unweak (sim-unbox sim)     = {!   !}
-- sim-unweak (sim-weak sim wk)   = {!  !}

-- Simulation implies typing...
-- Seriously, can't agda figure this one out itself?
sit : (t₁ t₂ : Γ ⊢ B) → Δ ⊢ t₁ ~ t₂ ∶ A → A ≡ B
sit t₁         t₂         (sim-lock x _ _)                          = refl
sit t₁         t₂         (sim-var x)                               = refl
sit (ƛ t₁)     (ƛ t₂)     (sim-lam sim)  with sit t₁ t₂ sim
... | a =  {!   !}
sit _ _ _ = {!   !}
-- sit (box t₁)   (box t₂)   (sim-box sim)       rewrite sit t₁ t₂ sim = refl
-- sit (l₁ ∙ r₁)  (l₂ ∙ r₂)  (sim-app simₗ simᵣ) with sit l₁ l₂ simₗ
-- ... | refl = refl
-- sit (unbox t₁) (unbox t₂) (sim-unbox sim)     with sit t₁ t₂ sim 
-- ... | refl = refl

-- Obviously this proof will require some syntactic lemmas, and here they are.
private module lemmas where
    -- sim-weak : (t₁ t₂ : Γ ⊢ A) → Γ ⊆ Δ → Γ ⊢ t₁ ~ t₂ ∶ A → Σ[ t₁′ ∈ Δ ⊢ A ] Σ[ t₂′ ∈ Δ ⊢ A ] (Δ ⊢ t₁′ ~ t₂′ ∶ A)
    -- sim-weak t₁ t₂ ⊆-empty     sim = t₁ ⸲ t₂ ⸲ sim
    -- sim-weak t₁ t₂ (⊆-drop wk) sim with sim-weak t₁ t₂ wk sim
    -- ... | t₁′ ⸲ t₂′ ⸲ sim′ = {!  !} ⸲ {!   !} ⸲ {!  !}
    -- sim-weak t₁ t₂ (⊆-keep wk) sim = {! !} ⸲ {!   !} ⸲ {!   !}
    -- sim-weak t₁ t₂ (⊆-lock wk) sim = {!   !} ⸲ {!   !} ⸲ {!   !}

    -- ius-sub-keep : Γ , B , A  ⊢ sub           (sub-subs sub-refl a₁)  b₁ ~ sub           (sub-subs sub-refl a₂)  b₂ ∶ B
    --              → Γ , A      ⊢ sub (sub-keep (sub-subs sub-refl a₁)) b₁ ~ sub (sub-keep (sub-subs sub-refl a₂)) b₂ ∶ B
    -- ius-sub-keep = ?

open lemmas



-- The indistinguishability under substitution lemma.
-- God, this is disgusting, isn't it?
ius : (t₁ t₂ : Γ , B ⊢ A)
    → (a₁ a₂ : Γ     ⊢ B)  
    -----------------------------------
    → Γ , B ⊢ t₁        ~ t₂        ∶ A 
    → Γ     ⊢ a₁        ~ a₂        ∶ B
    -----------------------------------
    → Γ     ⊢ t₁ [ a₁ ] ~ t₂ [ a₂ ] ∶ A
ius t₁ t₂ a₁ a₂ (sim-lock (is-ext ext) _ _) sim₂ = sim-lock ext (t₁ [ a₁ ]) (t₂ [ a₂ ])
---------------------------------------------------------------------------------------
ius t₁ t₂ a₁ a₂ (sim-var Z)     sim₂ = sim₂
ius t₁ t₂ a₁ a₂ (sim-var (S x)) sim₂ rewrite sub-refl-id-var (var x) refl with is∷-∈ x  
... | Γ₁ ⸲ Γ₂ ⸲ ext = sim-var x
--------------------------------------------
ius t₁ t₂ a₁ a₂ (sim-app  {t₁ = l₁} {t₁′ = l₂} {A = T} {B = U} {t₂ = r₁} {t₂′ = r₂} simₗ simᵣ) sim₂ with sit l₁ l₂ simₗ | sit r₁ r₂ simᵣ
... | refl | refl = sim-app (ius l₁ l₂ a₁ a₂ simₗ sim₂) (ius r₁ r₂ a₁ a₂ simᵣ sim₂)
-----------------------------------------------------------------------------------
ius t₁ t₂ a₁ a₂ (sim-lam {t = b₁} {t′ = b₂} sim₁) sim₂ with sit b₁ b₂ sim₁ 
... | refl = let

    lem = ius b₁ {!   !} {!   !} {!   !} sim₁ {!   !}
    in sim-lam {!   !}
---------------------------------------------------
ius t₁ t₂ a₁ a₂ (sim-box {t = b₁} {t′ = b₂} sim₁) sim₂ with sit b₁ b₂ sim₁
... | refl = sim-box {!   !}

-- Non-interference for the Fitch calculus
-- ni : Γ ⊢ t₁ ~ t₂ ∶ A 
--    → t₁ →β t₁′ 
--    ------------------------------------------------------
--    → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
-- ni sim β■ = {!   !}
-- ni sim βƛ = {!   !}
-- ni sim (ξappl step) = {!   !}
-- ni sim (ξappr step) = {!   !}
-- ni sim (ξbox step) = {!   !}
-- ni sim (ξunbox step) = {!   !}  
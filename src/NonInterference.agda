module NonInterference where
open import Base
open import LFExt
open import Terms
open import Trans
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Function
open import Data.Bool 
open import Data.Nat
open import Data.Product renaming (_,_ to _⸲_)
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
... | refl = {!   !}
---------------------------------------------------
ius t₁ t₂ a₁ a₂ (sim-box {t = b₁} {t′ = b₂} sim₁) sim₂ with sit b₁ b₂ sim₁
... | refl = sim-box {!   !}

-- The first leg of non-interference. This says related terms reduce together.
-- β~ : Γ ⊢ t₁ ~ t₂ ∶ A
--    → t₁ →β t₁′
--    -----------------
--    → Σ[ t₂′ ∈ Γ ⊢ A ] t₂ →β t₂′
-- β~ sim β■ = {!   !}
-- β~ sim βƛ = {!   !}
-- β~ sim (ξappl step)  = {!   !}
-- β~ sim (ξappr step)  = {!   !}
-- β~ sim (ξbox step)   = {!   !}
-- β~ sim (ξunbox step) = {!   !}   

-- Non-interference for the Fitch calculus
-- ni : Γ ⊢ t₁ ~ t₂ ∶ A 
--    → t₁ →β t₁′ 
--    ------------------------------------------------------
--    → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
-- ni sim β■ = {!   !}
-- ni sim βƛ = {!   !}
-- ni (sim-lock x .(_ ∙ _) _) (ξappl step) = {!   !}
-- ni (sim-app simₗ simᵣ)     (ξappl step) = {!   !} ⸲ {!   !} ⸲ {!   !}
-- ni sim (ξappr step)  = {!   !}
-- ni sim (ξbox step)   = {!   !}
-- ni sim (ξunbox step) = {!   !} 

identity : (Γ : Context) → (A : Type) → Γ ⊢ A ⇒ A
identity _ _ = ƛ (var Z)

sim-bad : ∅ ■ ⊢ identity _ _ ∙ (nat 0) ~ (nat 0) ∶ Nat 
sim-bad = sim-lock is-nil ((ƛ var Z) ∙ nat 0) (nat 0)

red-bad : identity (∅ ■) _ ∙ (nat 0) →β (nat 0)
red-bad = βƛ

issue : ¬(∀{Γ : Context} {A : Type} {t₁ t₂ t₁′ : Γ ⊢ A}
          → Γ ⊢ t₁ ~ t₂ ∶ A 
          → t₁ →β t₁′ 
          ------------------------------------------------------
          → Σ[ t₂′ ∈ Γ ⊢ A ] ((t₂ →β t₂′) × (Γ ⊢ t₁′ ~ t₂′ ∶ A))
        )
issue ni with ni sim-bad red-bad
... | _ ⸲ () ⸲ _
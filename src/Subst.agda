{-# OPTIONS --allow-unsolved-metas #-}
module Subst where
open import Base
open import Terms
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Unit

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ : Context

-- -- Extension lemma, for when we go 'under' binders.
-- ext : Γ₁ ⊆■ Γ₂ → Γ₁ , B ⊆■ Γ₂ , B
-- ext ρ Z■      =  Z■
-- ext ρ (S■ x)  =  S■ (ρ x)

-- -- Extension lemma, for when we go under boxes!
-- ext■ : Γ₁ ⊆■ Γ₂ → Γ₁ ■ ⊆■ Γ₂ ■
-- ext■ ρ (L■ x) = L■ ρ x

-- -- And the inverse.
-- ■ext : Γ₁ ■ ⊆■ Γ₂ ■ → Γ₁ ⊆■ Γ₂
-- ■ext ρ x with ρ (L■ x)
-- ... | L■ x = x

-- -- Renamings preserve locklessness.
-- ¬■-Γ→¬■-ρΓ : Γ₁ ⊆■ Γ₂ → F (lock?ᵇ Γ₁) → F (lock?ᵇ Γ₂)
-- ¬■-Γ→¬■-ρΓ {Γ₂ = ∅} ρ prf = tt
-- ¬■-Γ→¬■-ρΓ ρ prf with prf 
-- ... | a = {!   !}

-- -- Commute renamings and boxes
-- ext-■ : ∀ {Γ₁ Γ₂} → (∀ {A} → A ∈ Γ₁ ■ → A ∈ Γ₂ ■) → (∀ {A} → A ∈ Γ₁ → A ∈ Γ₂)
-- ext-■ {Γ , A} {∅} ρ Z = {!  !}
-- ext-■ {Γ , A} {Γ₂ , x} ρ Z = {!   !}
-- ext-■ {Γ , A} {Γ₂ ■} ρ Z = {!   !}
-- ext-■ ρ (S x) = ext-■ (λ ()) x


-- Extension, but for terms..!
-- ext′ : (∀ {A}   → A ∈■ Γ₁     →     Γ₂ ⊢ A)
--      --------------------------------------
--      → (∀ {A B} → A ∈■ Γ₁ , B → Γ₂ , B ⊢ A)
-- ext′ σ Z■      =  var Z
-- ext′ σ (S■ x)  =  ren S■_ (σ x)

-- -- Again, now for boxes.
-- ext■′ : (∀ {A} → A ∈■ Γ₁   → Γ₂ ⊢ A)
--       ----------------------------------
--       → (∀ {A} → A ∈■ Γ₁ ■ → Γ₂ ■ ⊢ A)
-- ext■′ σ (L■ Z■) = {!   !}
-- ext■′ σ (L■ (S■ a)) = {!   !}
-- ext■′ σ (L■ (L■ a)) = {!   !}

-- Extension lemma for variables, when we go under a binder
ƛext : (∀ {A}   → A ∈ Γ     →     Δ ⊢ A)
     -----------------------------------
     → (∀ {A B} → A ∈ Γ , B → Δ , B ⊢ A)
ƛext σ Z     = var Z
ƛext σ (S x) = weakening (sub-drop ⊆-refl) (σ x)

-- Extension lemma for boxes, for when we go under a box
-- ■ext : (∀ {A}   → A ∈ Γ  →    Δ ⊢ A)
--     --------------------------------------
--     → (∀ {A B} → A ∈ Γ ■ → Δ ■ ⊢ A)
-- ■ext σ ()


-- lem-idk : (∀ {A} → A ∈ Γ → Δ ⊢ A) 
--         → Γ is Γ₁ ■ ∷ Γ₂
--         -------------------------
--         → Δ is {!   !} ∷ {!   !}
-- lem-idk = {!   !}

sub : (∀ {A} → A ∈ Γ  → Δ ⊢ A)
    --------------------------
    → (∀ {A} → Γ ⊢ A  → Δ ⊢ A)
sub σ (nat n)   = nat n
sub σ (var x)   = σ x
sub σ (ƛ t)     = ƛ sub (ƛext σ) t
sub σ (l ∙ r)   = sub σ l ∙ sub σ r
sub σ (box t)   = box (sub (λ ()) t)
sub σ (unbox {ext = e} t) 
    = unbox {ext = {!   !}} (sub {!   !} t)
    where
        -- lem-irrel : (∀ {A} → A ∈ Γ  → Δ ⊢ A) 
        --           → Γ is Γ₁ ■ ∷ Γ₂
        --           -------------------------
        --           → (∀ {A} → A ∈ Γ₁ → Γ₁ ⊢ A)
        -- lem-irrel σ (is-ext ext) x = lem-irrel (λ z → σ (S z)) ext x
        -- lem-irrel σ is-nil (S x)   = var (S x)
        -- lem-irrel σ is-nil Z       = var Z


-- Type preserving substitution on the first free variable (used for β-reduction)
-- _[_] : ∀ {Δ T U} → Δ , U ⊢ T → Δ ⊢ U → Δ ⊢ T
-- _[_] {Δ} {T} {U} t₁ t₂ = sub {Γ₁ = Δ , U} {Γ₂ = Δ} (σ-wk σ) {T} t₁ 
--     where
--     σ-wk : ∀ {α} → (α ∈ Δ , U → Δ ⊢ α) → (α ∈■ Δ , U → Δ ⊢ α) 
--     σ-wk σ Z■ = σ Z
--     σ-wk σ (S■ x) = σ (S ∈-str {prf = {!   !}} x)

--     σ : ∀ {α} → α ∈ Δ , U → Δ ⊢ α
--     σ Z     = t₂
--     σ (S x) = var x
   
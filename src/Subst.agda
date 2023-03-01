{-# OPTIONS --allow-unsolved-metas #-}
module Subst where
open import Base
open import Terms
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Unit

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ Γ′ : Context

{-- 
Acc ~ is ∷
lCtx ~ ←■
rCtx ~ ■→
new ~ new (wtf is new)
factorWk ~ sliceLeft ~ is∷-←■weak
factorExt ~ wkLFExt ~ is∷Δweak
--}

infix 3 σ_⇒_
-- The type of substitutions, a substitution relation
data σ_⇒_ : Context → Context → Set where
    σ∅ : σ Γ  ⇒ ∅
    σx : σ Γ  ⇒ Δ → Γ ⊢ A        → σ Γ ⇒ Δ , A
    σ■ : σ Γ₁ ⇒ Δ → Γ is Γ₁ ∷ Γ₂ → σ Γ ⇒ Δ ■

-- Apply a weakening to a substitution
-- σ-weak : Γ ⊆ Γ′ → σ Γ ⇒ Δ → σ Γ′ ⇒ Δ
-- σ-weak wk σ∅         = σ∅
-- σ-weak wk (σx σ t)   = σx (σ-weak wk σ) (weakening wk t)
-- σ-weak wk (σ■ σ ext) = σ■ (σ-weak (is∷-←■weak {!   !} {!   !}) σ) (is∷-Δweak {!   !} wk)

-- Extension lemma for variables, when we go under a binder
ƛext : σ Γ ⇒ Δ → σ Γ , B ⇒ Δ , B
ƛext σ∅ = σx σ∅ (var Z)
ƛext (σx σ x) = σx {!   !} {!   !}
ƛext (σ■ σ x) = {!   !}


sub : σ Γ ⇒ Δ → Γ ⊢ A → Δ ⊢ A
sub σ t = {!   !}
-- sub σ (nat n) = nat n
-- sub σ (var x) = σ x
-- sub σ (ƛ t)   = ƛ sub (ƛext σ) t
-- sub σ (l ∙ r) = sub σ l ∙ sub σ r
-- sub σ (box t) = box (sub (λ ()) t)
-- sub σ (unbox {ext = e} t) 
--     = unbox {ext = {!   !}} (sub {!   !} t)
--     where
--         lem-irrel : (∀ {A} → A ∈ Γ  → Δ ⊢ A) 
--                   → Γ is Γ₁ ■ ∷ Γ₂
--                   -------------------------
--                   → (∀ {A} → A ∈ Γ₁ → Γ₁ ⊢ A)
--         lem-irrel σ (is-ext ext) x = lem-irrel (λ z → σ (S z)) ext x
--         lem-irrel σ is-nil (S x)   = var (S x)
--         lem-irrel σ is-nil Z       = var Z


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
         
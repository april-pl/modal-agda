{-# OPTIONS --allow-unsolved-metas #-}
module Subst where
open import Base
open import Terms
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to Prod)

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ Γ′ Δ′ : Context

{-- 
Acc ~ is ∷
lCtx ~ ←■
rCtx ~ ■→
new ~ new (wtf is new)
factorWk ~ sliceLeft ~ is∷-←■weak
factorExt ~ wkLFExt ~ is∷Δweak
--}

-- The type of replacements, either replacing or keeping free variables in a context.
data Sub : Context → Context → Set where
    -- Base substitution
    sub-base : Sub ∅ ∅ 

    -- Under locks
    sub-lock : Sub Γ Δ          → Sub (Γ ■)   (Δ ■)
    -- Extend a substitution, keeping the term
    sub-keep : Sub Γ Δ          → Sub (Γ , B) (Δ , B)
    -- Extend a substitution with a new term
    sub-subs : Sub Γ Δ → Δ ⊢ B  → Sub (Γ , B) Δ
    -- Weaken a substitution
    sub-trim : Sub Γ Δ → Δ ⊆ Δ′ → Sub Γ Δ′

-- Substitutions are into subcontexts
-- sub-⊆ : Sub Γ Δ → Δ ⊆ Γ
-- sub-⊆ sub-base         = ⊆-empty
-- sub-⊆ (sub-lock sub)   = ⊆-lock (sub-⊆ sub)
-- sub-⊆ (sub-keep sub)   = ⊆-keep (sub-⊆ sub)
-- sub-⊆ (sub-subs sub x) = ⊆-drop (sub-⊆ sub)

-- Weaken the result of a substitution
-- sub-weak : Sub Γ Δ → Δ ⊆ Δ′ → Sub Γ Δ′
-- sub-weak sub ⊆-empty     = sub
-- sub-weak sub (⊆-drop wk) = {!   !}
-- sub-weak (sub-keep sub) (⊆-keep wk) = sub-keep (sub-weak sub wk)
-- sub-weak (sub-subs sub x) (⊆-keep wk) = {!   !}
-- sub-weak (sub-lock sub) (⊆-lock wk) = sub-lock (sub-weak sub wk)
-- sub-weak (sub-subs sub x) (⊆-lock wk) = {!   !}

-- Apply a weakening to a substitution
-- σ-weak : Γ ⊆ Γ′ → σ Γ ⇒ Δ → σ Γ′ ⇒ Δ
-- σ-weak wk σ∅         = σ∅
-- σ-weak wk (σx σ t)   = σx (σ-weak wk σ) (weakening wk t)
-- σ-weak wk (σ■ σ ext) = σ■ (σ-weak (is∷-←■weak {!   !} {!   !}) σ) (is∷-Δweak {!   !} wk)

sub : Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
sub (sub-trim σ wk) t = weakening wk (sub σ t)
--------------------------------------------------------------
sub (sub-keep σ)    (var Z)     = var Z
sub (sub-subs σ u)  (var Z)     = u
sub (sub-keep σ)    (var (S x)) = sub (sub-trim σ (⊆-drop ⊆-refl)) (var x)
sub (sub-subs σ u)  (var (S x)) = sub σ (var x)
-----------------------------------------------
sub σ (nat n)   = nat n
sub σ (ƛ t)     = ƛ sub (sub-keep σ) t
sub σ (box t)   = box (sub (sub-lock σ) t)
sub σ (l ∙ r)   = sub σ l ∙ sub σ r
-----------------------------------
sub (sub-lock σ)   (unbox {ext = e} t) with is∷-Γ■ e 
... | Prod refl refl = {!   !}
sub (sub-keep σ)   (unbox {ext = e} t) = {!   !}
sub (sub-subs σ u) (unbox {ext = e} t) = {!   !}

-- -- Type preserving substitution on the first free variable (used for β-reduction)
-- -- _[_] : ∀ {Δ T U} → Δ , U ⊢ T → Δ ⊢ U → Δ ⊢ T
-- -- _[_] {Δ} {T} {U} t₁ t₂ = sub {Γ₁ = Δ , U} {Γ₂ = Δ} (σ-wk σ) {T} t₁ 
-- --     where
-- --     σ-wk : ∀ {α} → (α ∈ Δ , U → Δ ⊢ α) → (α ∈■ Δ , U → Δ ⊢ α) 
-- --     σ-wk σ Z■ = σ Z
-- --     σ-wk σ (S■ x) = σ (S ∈-str {prf = {!   !}} x)

-- --     σ : ∀ {α} → α ∈ Δ , U → Δ ⊢ α
-- --     σ Z     = t₂
-- --     σ (S x) = var x
                 
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

sub-refl : Sub Γ Γ
sub-refl {Γ = ∅}     = sub-base
sub-refl {Γ = Γ , x} = sub-keep sub-refl
sub-refl {Γ = Γ ■}   = sub-lock sub-refl

-- Useful lemma for proofs involving the unbox constructor.
-- ... since extensions of this type are produced by it,
-- and we need one in order to put everyhting back together again.
is∷-Δsub : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Δ is (←■ Δ) ■ ∷ (■→ Δ)
is∷-Δsub ext          (sub-trim sub wk) = is∷-Δweak (is∷-Δsub ext sub) wk
is∷-Δsub ext          (sub-lock sub)    = is-nil
is∷-Δsub (is-ext ext) (sub-keep sub)    = is-ext (is∷-Δsub ext sub)
is∷-Δsub (is-ext ext) (sub-subs sub t)  = is∷-Δsub ext sub

private module lemmas where
    -- Weakening is congruent with the left-of-lock operation
    lemma-⊆-←■ : Γ ⊆ Δ → ←■ Γ ⊆ ←■ Δ 
    lemma-⊆-←■ ⊆-empty     = ⊆-empty
    lemma-⊆-←■ (⊆-drop wk) = lemma-⊆-←■ wk
    lemma-⊆-←■ (⊆-keep wk) = lemma-⊆-←■ wk
    lemma-⊆-←■ (⊆-lock wk) = wk

    -- Same as the above, but through substitutions
    lemma-sub : Δ ⊆ Δ′ → Sub Γ (←■ Δ) → Sub Γ (←■ Δ′)
    lemma-sub ⊆-empty sub = sub
    lemma-sub (⊆-drop wk) sub = lemma-sub wk sub
    lemma-sub (⊆-keep wk) sub = lemma-sub wk sub
    lemma-sub (⊆-lock wk) sub = sub-trim sub wk

    lemma-, = is∷-■,

open lemmas

-- Much like before. This gives us a substitution that...
-- ... only works left of a lock, from one produced by unbox.
-- Γ   is   (Γ₁) ■ ∷ Γ₂
-- ↓         ↓↓
-- Δ   is   (Δ₁) ■ ∷ Γ₂
sub-←■ : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Sub Γ₁ (←■ Δ)
sub-←■ ext sub with is∷-Δsub ext sub
sub-←■ ext₁          (sub-trim sub wk) | ext₂        = lemma-sub wk (sub-←■ ext₁ sub)
sub-←■ is-nil        (sub-lock sub)    | _           = sub
sub-←■ (is-ext ext₁) (sub-keep sub)    | is-ext ext₂ = sub-←■ ext₁ sub
sub-←■ (is-ext ext₁) (sub-subs sub t)  | ext₂        = sub-←■ ext₁ sub


-- Parallel substitution!
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
sub σ (unbox {ext = e} t) 
    -- In this case, instead of just passing arguments we have to obey weakening
    -- See the above lemmas which transform subs and contexts respectively.
    = unbox {ext = is∷-Δsub e σ} (sub (sub-←■ e σ) t)

-- Single variable substitution, from the above.
-- _[_/_] : Γ ⊢ A → Δ ⊢ B

infix 4 _[_]
-- Single variable substitution on the first free variable.
-- Used for β-reduction... obviously.
_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
t₁ [ t₂ ] = sub (sub-subs sub-refl t₂) t₁

-- Some lemmas about substitution.

private variable
    x y     : _ ∈ _
    t t₁ t₂ : _ ⊢ _

-- -- Single substitution on a non-Z variable is the identity
-- sub[]-≢ : (x : _ ∈ _) → (t₁ : Γ , B ⊢ A) → (t₂ : Γ ⊢ B) → t₁ ≡ var (S x) → _[_] t₁ t₂ ≡ t₁
-- sub[]-≢ refl = {!   !} 

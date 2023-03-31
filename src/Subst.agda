{-# OPTIONS --allow-unsolved-metas #-}
module Subst where
open import Base
open import Terms
open import LFExt
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to Prod)

private variable
    A B : Type
    Γ Δ θ Γ₁ Γ₂ Γ′ Δ′ : Context

{-- 
Acc ~ is ∷
lCtx ~ ←■
rCtx ~ ■→
new ~ new (wtf is new)
factorWk ~ sliceLeft ~ is∷-←■weak
factorExt ~ wkLFExt ~ is∷Δweak
--}

infixr 3 _⇉_
infixr 4 _•■
infixr 4 _•_
-- The type of substitutions, done properly this time
data _⇉_ : Context → Context → Set where
    -- Base substitution
    ε : Γ ⇉ ∅
    -- Weaken a substitution
    p : Γ , A ⇉ Γ 

    -- Under locks
    _•■ : Γ ⇉ Δ         → Γ ■ ⇉ Δ ■
    -- Extend a substitution with a term
    _•_ : Γ ⇉ Δ → Δ ⊢ A → Γ ⇉ Δ , A
    -- Compose substitutions
    _◦_ : Γ ⇉ Δ → Δ ⇉ θ → Γ ⇉ θ

-- q : Context → 

-- This thing
σ+ : Γ ⇉ Δ → Γ , A ⇉ Δ , A
σ+ σ = (p ◦ σ) • {!   !}

sub-refl : Γ ⇉ Γ
sub-refl {∅}     = ε
sub-refl {Γ , x} = σ+ sub-refl
sub-refl {Γ ■}   = sub-refl •■

-- Useful lemma for proofs involving the unbox constructor.
-- ... since extensions of this type are produced by it,
-- and we need one in order to put everyhting back together again.
-- is∷-Δsub : Γ is Γ₁ ■ ∷ Γ₂ → Γ ⇉ Δ → Δ is (←■ Δ) ■ ∷ (■→ Δ)

-- is∷-Δsub ext (sub ◦ sub₁) = {!   !}
-- is∷-Δsub : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Δ is (←■ Δ) ■ ∷ (■→ Δ)
-- is∷-Δsub ext          (sub-lock sub)   = is-nil
-- is∷-Δsub is-nil       sub-weak         = is-ext is-nil
-- is∷-Δsub (is-ext ext) sub-weak         = is-ext (is∷-Δsub ext sub-weak)
-- is∷-Δsub (is-ext ext) (sub-extn sub x) = is∷-Δsub ext sub

-- private module lemmas where
--     -- Weakening is congruent with the left-of-lock operation
--     lemma-⊆-←■ : Γ ⊆ Δ → ←■ Γ ⊆ ←■ Δ 
--     lemma-⊆-←■ ⊆-empty     = ⊆-empty
--     lemma-⊆-←■ (⊆-drop wk) = lemma-⊆-←■ wk
--     lemma-⊆-←■ (⊆-keep wk) = lemma-⊆-←■ wk
--     lemma-⊆-←■ (⊆-lock wk) = wk

--     -- Same as the above, but through substitutions
--     lemma-sub : Δ ⊆ Δ′ → Sub Γ (←■ Δ) → Sub Γ (←■ Δ′)
--     lemma-sub ⊆-empty     sub = sub
--     lemma-sub (⊆-drop wk) sub = lemma-sub wk sub
--     lemma-sub (⊆-keep wk) sub = lemma-sub wk sub
--     lemma-sub (⊆-lock wk) sub = sub-trim sub wk

--     lemma-, = is∷-■,

-- open lemmas

-- Much like before. This gives us a substitution that...
-- ... only works left of a lock, from one produced by unbox.
-- Γ   is   (Γ₁) ■ ∷ Γ₂
-- ↓         ↓↓
-- Δ   is   (Δ₁) ■ ∷ Γ₂
-- sub-←■ : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Sub Γ₁ (←■ Δ)
-- sub-←■ ext sub with is∷-Δsub ext sub
-- ... | ext₂ = {!   !}
-- sub-←■ ext sub with is∷-Δsub ext sub
-- sub-←■ ext₁          (sub-trim sub wk) | ext₂        = lemma-sub wk (sub-←■ ext₁ sub)
-- sub-←■ is-nil        (sub-lock sub)    | _           = sub
-- sub-←■ (is-ext ext₁) (sub-keep sub)    | is-ext ext₂ = sub-←■ ext₁ sub
-- sub-←■ (is-ext ext₁) (sub-subs sub t)  | ext₂        = sub-←■ ext₁ sub

-- Parallel substitution!
-- sub : Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
-- sub σ (nat x) = nat x
-- --------------------------------
-- sub sub-weak       (var Z)     = var (S Z)
-- sub (sub-extn σ x) (var Z)     = x
-- sub sub-weak       (var (S x)) = var (S (S x))
-- sub (sub-extn σ _) (var (S x)) = sub σ (var x)
-- -----------------------------------------------
-- sub σ (ƛ t) = ƛ sub {!   !} t
-- sub σ (box t) = box (sub (sub-lock σ) t)
-- sub σ (unbox t) = {!   !}
-- sub σ (l ∙ r) = sub σ l ∙ sub σ r
-- sub (sub-trim σ wk) t = weakening wk (sub σ t)
-- --------------------------------------------------------------
-- sub (sub-keep σ)    (var Z)     = var Z
-- sub (sub-subs σ u)  (var Z)     = u
-- sub (sub-keep σ)    (var (S x)) = sub (sub-trim σ (⊆-drop ⊆-refl)) (var x)
-- sub (sub-subs σ u)  (var (S x)) = sub σ (var x)
-- -----------------------------------------------
-- sub σ (nat n)   = nat n
-- sub σ (ƛ t)     = ƛ sub (sub-keep σ) t
-- sub σ (box t)   = box (sub (sub-lock σ) t)
-- sub σ (l ∙ r)   = sub σ l ∙ sub σ r
-- -----------------------------------
-- sub σ (unbox {ext = e} t) 
--     -- In this case, instead of just passing arguments we have to obey weakening
--     -- See the above lemmas which transform subs and contexts respectively.
--     = unbox {ext = is∷-Δsub e σ} (sub (sub-←■ e σ) t)

-- private variable
--     x y     : _ ∈ _
--     t t₁ t₂ : _ ⊢ _


-- infix 5 _[_]
-- -- Single variable substitution on the first free variable.
-- -- Used for β-reduction... obviously.
-- _[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
-- t₁ [ t₂ ] = sub (sub-subs sub-refl t₂) t₁

-- -- infix 5 _[_/_]′
-- -- -- Single variable substitution, from the above.
-- -- _[_/_]′ : Γ ⊢ A → (Γ₁ ∷ Γ₂) ⊢ B → Γ is Γ₁ , B ∷ Γ₂ → (Γ₁ ∷ Γ₂) ⊢ A
-- -- t₁ [ t₂ / is-nil ]′   = t₁ [ t₂ ] 
-- -- t₁ [ t₂ / is-ext x ]′ = sub (sub-keep (build-sub x (sub-subs sub-refl {!   !}))) t₁ 
-- --     where
-- --     build-sub : Γ is Γ₁ , A ∷ Γ₂ → Sub (Γ₁ , A) Γ₁ → Sub Γ (Γ₁ ∷ Γ₂)
-- --     build-sub (is-ext ext) sub = sub-keep (build-sub ext sub)
-- --     build-sub is-nil       sub = sub

-- -- Some lemmas about substitution.
-- private module lemmas′ where
--     -- We need this lemma to prove the below
--     ⊆-refl-id : (x : A ∈ Γ) → Γ-weak ⊆-refl x ≡ x
--     ⊆-refl-id {Γ = Γ , B} (S x) rewrite ⊆-refl-id x = refl
--     ⊆-refl-id {Γ = Γ , B} Z                         = refl

-- open lemmas′

-- -- Γ , A ⊢ sub (sub-keep (sub-subs sub-refl a₁)) b₁ ~ sub (sub-keep (sub-subs sub-refl a₂)) b₂ ∶ B
-- -- 
-- -- sub-keep-ƛ : () ≡ 

-- -- sub-ƛ : {t₁ : Γ , A ⊢ B} → (ƛ t₁) [ t₂ ] ≡ ƛ (t₁ [ t₂ ])
-- -- sub-ƛ {t₁ = t₁} {t₂ = t₂} = {! !}

-- -- Substitution with sub-refl doesn't do anything - special case for variables.
-- -- Probably true in general, but the case for unbox is annoying.
-- -- We don't need it so this is way easier to prove.
-- sub-refl-id-var : (t : Γ ⊢ A) → t ≡ var x → sub sub-refl t ≡ t
-- sub-refl-id-var (var Z)     refl = refl
-- sub-refl-id-var (var (S x)) refl 
--     rewrite sub-refl-id-var (var x) refl | ⊆-refl-id x = refl
    
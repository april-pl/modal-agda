{-# OPTIONS --allow-unsolved-metas #-}
module Subst where
open import Base
open import Terms
open import LFExt
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _،_)

private variable
    A B : Type
    Γ Δ θ Γ₁ Γ₂ Γ′ Δ₁ Δ₂ Δ′ : Context

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

data _⇉_ : Context → Context → Set where
    -- Base substitution
    ε : Γ ⇉ ∅

    -- Weaken a substitution
    wk  : Γ ⊆ Γ′        → Γ′ ⇉ Γ 
    -- Under locks
    _•■ : Γ ⇉ Δ         → Γ ■ ⇉ Δ ■
    -- Extend a substitution with a term
    _•_ : Γ ⇉ Δ → Γ ⊢ A → Γ ⇉ Δ , A

p : Γ , A ⇉ Γ
p = wk (⊆-drop ⊆-refl)

-- Strengthen the domain of a substitution
⇉-st : Γ ⇉ Δ → Δ′ ⊆ Δ → Γ ⇉ Δ′
⇉-st _       ⊆-empty    = ε
⇉-st (wk x)  w          = wk (⊆-assoc w x)
⇉-st (σ •■)  (⊆-lock w) = ⇉-st σ w •■
⇉-st (σ • x) (⊆-drop w) = ⇉-st σ w
⇉-st (σ • x) (⊆-keep w) = ⇉-st σ w • x

⇉-refl : Γ ⇉ Γ
⇉-refl {∅}     = ε
⇉-refl {Γ ■}   = ⇉-refl •■
⇉-refl {Γ , x} = p • var Z

-- Useful lemma for proofs involving the unbox constructor.
-- ... since extensions of this type are produced by it,
-- and we need one in order to put everyhting back together again.
is∷-Δsub : Δ is Δ₁ ■ ∷ Δ₂ → Γ ⇉ Δ → Γ is (←■ Γ) ■ ∷ (■→ Γ)
is∷-Δsub is-nil (wk (⊆-drop w))       = is-ext (is∷-Δsub is-nil (wk w))
is∷-Δsub is-nil (wk (⊆-lock w))       = is-nil
is∷-Δsub is-nil (σ •■)                = is-nil
is∷-Δsub (is-ext ext) (wk (⊆-drop w)) = is-ext (is∷-Δsub (is-ext ext) (wk w))
is∷-Δsub (is-ext ext) (wk (⊆-keep w)) = is-ext (is∷-Δsub ext (wk w))
is∷-Δsub (is-ext ext) (σ • t)         = is∷-Δsub ext σ

-- Much like before. This gives us a substitution that...
-- ... only works left of a lock, from one produced by unbox.
-- Γ   is   (Γ₁) ■ ∷ Γ₂
-- ↓         ↓↓
-- Δ   is   (Δ₁) ■ ∷ Γ₂
sub-←■ : Δ is Δ₁ ■ ∷ Δ₂ → Γ ⇉ Δ → (←■ Γ) ⇉ Δ₁
sub-←■ is-nil (wk w) with ■⊆′ w 
... | Γ₁ ، Γ₂ ، ext  with is∷-←■ ext
... | refl           = wk (⊆-←■ w)
sub-←■ is-nil (σ •■) = σ
sub-←■ (is-ext ext) (wk w) with is∷-←■ ext
... | refl = wk (⊆-←■ w) 
sub-←■ (is-ext ext) (σ • x) = sub-←■ ext σ

-- I hate to do this but this is fairly theoretically grounded so it feels OK
{-# TERMINATING #-}
mutual 
    _◦_ : Δ ⇉ θ → Γ ⇉ Δ → Γ ⇉ θ
    sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A

    σ+  : Γ ⇉ Δ → Γ , A ⇉ Δ , A
    σ+ σ = (σ ◦ p) • (var Z)

    -- Parallel substitution, defined mutually recursively with composition
    sub σ (nat x) = nat x
    -------------------------
    sub (wk w)  (var Z)     = var (Γ-weak w Z)
    sub (σ • t) (var Z)     = t
    sub σ       (var (S x)) = sub (p ◦ σ) (var x)
    ---------------------------------------
    sub σ (ƛ t)   = ƛ sub (σ+ σ) t
    sub σ (box t) = box (sub (σ •■) t)
    sub σ (l ∙ r) = sub σ l ∙ sub σ r
    -------------------------------------------------
    sub σ (unbox {ext = e} t) = unbox {ext = is∷-Δsub e σ} (sub (sub-←■ e σ) t)
    
    -- Compose substitutions
    ε       ◦ τ = ε
    wk w    ◦ τ = ⇉-st τ w
    (σ • t) ◦ τ         = (σ ◦ τ) • sub τ t
    (σ •■)  ◦ wk w with ■⊆′ w | w
    ... | Γ₁  ، ∅ ، is-nil     | ⊆-lock w = (σ ◦ wk w) •■
    ... | _   ، _ ، is-ext ext | w        = (σ •■) ◦ wk w
    (σ •■) ◦ (τ •■) = (σ ◦ τ) •■

sub-refl : Γ ⇉ Γ
sub-refl {∅}     = ε
sub-refl {Γ , x} = σ+ sub-refl
sub-refl {Γ ■}   = sub-refl •■

infix 5 _[_]
-- Single variable substitution on the first free variable.
-- Used for β-reduction... obviously.
_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
t₁ [ t₂ ] = sub (sub-refl • t₂) t₁

-- -- -- infix 5 _[_/_]′
-- -- -- -- Single variable substitution, from the above.
-- -- -- _[_/_]′ : Γ ⊢ A → (Γ₁ ∷ Γ₂) ⊢ B → Γ is Γ₁ , B ∷ Γ₂ → (Γ₁ ∷ Γ₂) ⊢ A
-- -- -- t₁ [ t₂ / is-nil ]′   = t₁ [ t₂ ] 
-- -- -- t₁ [ t₂ / is-ext x ]′ = sub (sub-keep (build-sub x (sub-subs sub-refl {!   !}))) t₁ 
-- -- --     where
-- -- --     build-sub : Γ is Γ₁ , A ∷ Γ₂ → Sub (Γ₁ , A) Γ₁ → Sub Γ (Γ₁ ∷ Γ₂)
-- -- --     build-sub (is-ext ext) sub = sub-keep (build-sub ext sub)
-- -- --     build-sub is-nil       sub = sub

-- Some lemmas about substitution.
private module lemmas where
    -- We need this lemma to prove the below
    ⊆-refl-id : (x : A ∈ Γ) → Γ-weak ⊆-refl x ≡ x
    ⊆-refl-id {Γ = Γ , B} (S x) rewrite ⊆-refl-id x = refl
    ⊆-refl-id {Γ = Γ , B} Z                         = refl

open lemmas

  
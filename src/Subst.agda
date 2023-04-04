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

-- Substitutions compose with weakenings in a certain way
-- ⇉-⊆ : Γ ⇉ Δ → θ ⊆ Δ → θ ⊆ Γ
-- ⇉-⊆ ε       ⊆-empty = {!   !}
-- ⇉-⊆ (wk x)  w  = ⊆-assoc w x
-- ⇉-⊆ (σ •■)  w with ⊆■ w | w
-- ... | θ′ ، refl | ⊆-lock w′ = ⊆-lock {! w′ !}
-- ⇉-⊆ (σ • x) (⊆-drop w) = ⇉-⊆ σ w
-- ⇉-⊆ (σ • x) (⊆-keep w) = {!  !}

-- Strengthen the domain of a substitution
⇉-st : Γ ⇉ Δ → Δ′ ⊆ Δ → Γ ⇉ Δ′
⇉-st ε       ⊆-empty    = ε
⇉-st (wk x)  w          = wk (⊆-assoc w x)
⇉-st (σ •■)  (⊆-lock w) = ⇉-st σ w •■
⇉-st (σ • x) (⊆-drop w) = ⇉-st σ w
⇉-st (σ • x) (⊆-keep w) = ⇉-st σ w • x 

-- Weaken the codomain of a substitution
-- ⇉-wk : Γ ⇉ Δ → Γ ⊆ Γ′ → Γ′ ⇉ Δ
-- ⇉-wk ε w = ε
-- ⇉-wk (wk x) w = wk (⊆-assoc x w)
-- ⇉-wk (σ •■) (⊆-drop w) with ■⊆′ w | w
-- ... | Δ₁₁ ، ∅     ، ext@is-nil     | ⊆-lock w′ = wk (⊆-drop (⊆-lock (⊆-assoc {!   !} w′)))
-- ... | Δ₁₁ ، _ , _ ، is-ext ext | w′ = {!   !}
-- ⇉-wk (σ •■) (⊆-lock w) = ⇉-wk σ w •■
-- ⇉-wk (σ • t) w = 
--     let a = ⇉-wk σ w
--         b = ⇉-st a {!   !}
--     in wk ({!   !})


interleaved mutual 
    -- Idea - there is a lock in Γ and we can do that case
    -- Otherwise we just recurse and tag stuff onto the end which we can do
    lemma : Γ′ ⇉ Δ → (Γ′ ■) ⊆ Γ → Γ ⇉ Δ ■
    _◦_ : Δ ⇉ θ → Γ ⇉ Δ → Γ ⇉ θ
    
    lemma σ w with ■⊆′ w | w 
    ... | Γ₁ ، ∅      ، is-nil     | ⊆-lock w′ = (σ ◦ wk w′) •■
    ... | Γ₁ ، Γ₂ , B ، is-ext ext | ⊆-drop w′ = 
        let rec = lemma σ w′
        in {!   !}

    -- Compose substitutions
    ε       ◦ τ = ε
    wk w    ◦ τ = ⇉-st τ w
    (σ • x) ◦ τ = (σ ◦ τ) • {!   !}

    (σ •■) ◦ wk w = lemma σ w
    -- ... | ca ، cb ، ext | asdf = {!   !}
    -- -- ... | Δ₁ ، ∅      ، is-nil     | ⊆-lock w′ = (σ ◦ wk w′) •■
    -- -- ... | Δ₁ ، Δ₂ , B ، is-ext ext | ⊆-drop w′ = {!   !}
    (σ •■) ◦ (τ •■) = (σ ◦ τ) •■


-- ε       ◦ τ              = ε

-- wk w    ◦ ε rewrite ⊆∅ w = ε
-- wk w    ◦ wk x           = wk (⊆-assoc w x)
-- wk w    ◦ (τ •■)         with ⊆■ w | w
-- wk w    ◦ (τ •■)         | θ′ ، refl | ⊆-lock a = wk {!  !} •■
-- wk (⊆-drop w) ◦ (τ • x) = ⇉-st τ w
-- wk (⊆-keep w) ◦ (τ • x) = (wk w ◦ τ) • x

-- (σ • x) ◦ ε = {! σ !}
-- (σ • x) ◦ wk w = {!   !}
-- (σ • x) ◦ (τ •■) = {!   !}
-- (σ • x) ◦ (τ • x₁) = {!   !}

-- (σ •■) ◦ wk w   = {! !}
-- (σ •■) ◦ (τ •■) = (σ ◦ τ) •■

-- _◦_ : Δ ⇉ θ → Γ ⇉ Δ → Γ ⇉ θ
-- ε ◦ ε = {!   !} ◦ {!   !}
-- (σ • x) ◦ ε = {!   !} ◦ {!   !}

-- σ ◦ p = {!   !}
-- ε ◦ (τ •■) = {!   !}
-- σ ◦ (τ • x) = {!   !}

-- (σ •■) ◦ (τ •■) = (σ ◦ τ) •■
-- (σ • x) ◦ (τ •■) = {!   !}


-- -- f : Γ ⇉ Δ → A ∈ Δ → Γ ⊢ A
-- -- f p x = var (S x)
-- -- f (σ • t) Z = f σ x
-- -- f (σ • t) (S x) = {! (f σ x) ? !}

σ+ : Γ ⇉ Δ → Γ , A ⇉ Δ , A
σ+ {Δ} σ = (σ ◦ p) • var Z

-- sub-refl : Γ ⇉ Γ
-- sub-refl {∅}     = ε
-- sub-refl {Γ , x} = σ+ sub-refl
-- sub-refl {Γ ■}   = sub-refl •■

-- -- Useful lemma for proofs involving the unbox constructor.
-- -- ... since extensions of this type are produced by it,
-- -- and we need one in order to put everyhting back together again.
-- is∷-Δsub : Δ is Δ₁ ■ ∷ Δ₂ → Γ ⇉ Δ → Γ is (←■ Γ) ■ ∷ (■→ Γ)
-- is∷-Δsub ext p = {!  !}
-- is∷-Δsub ext (σ •■) = is-nil
-- is∷-Δsub ext (σ • x) = {!   !}
-- is∷-Δsub ext (σ ◦ τ) = is∷-Δsub (is∷-Δsub ext σ) τ
-- -- is∷-Δsub ext ε = {!   !}
-- -- is∷-Δsub ext p = {!   !}
-- -- is∷-Δsub ext (σ •■)  = is-nil
-- -- is∷-Δsub ext (σ • x) = is-ext (is∷-Δsub ext σ)
-- -- is∷-Δsub ext (σ ◦ τ) = is∷-Δsub (is∷-Δsub ext τ) σ

-- -- is∷-Δsub : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Δ is (←■ Δ) ■ ∷ (■→ Δ)
-- -- is∷-Δsub ext          (sub-lock sub)   = is-nil
-- -- is∷-Δsub is-nil       sub-weak         = is-ext is-nil
-- -- is∷-Δsub (is-ext ext) sub-weak         = is-ext (is∷-Δsub ext sub-weak)
-- -- is∷-Δsub (is-ext ext) (sub-extn sub x) = is∷-Δsub ext sub

-- private module lemmas where
--     -- lemma-σ-var : Γ ⇉ Δ → A ∈ Δ → A ∈ Γ
--     -- lemma-σ-var p x = S x
--     -- lemma-σ-var (σ • t) Z = {!   !}
--     -- lemma-σ-var (σ • t) (S x) = lemma-σ-var σ x
--     -- lemma-σ-var (σ ◦ τ) x = {!   !}

-- --     -- Weakening is congruent with the left-of-lock operation
--     lemma-⊆-←■ : Γ ⊆ Δ → ←■ Γ ⊆ ←■ Δ 
--     lemma-⊆-←■ ⊆-empty     = ⊆-empty
--     lemma-⊆-←■ (⊆-drop wk) = lemma-⊆-←■ wk
--     lemma-⊆-←■ (⊆-keep wk) = lemma-⊆-←■ wk
--     lemma-⊆-←■ (⊆-lock wk) = wk

--     -- Same as the above, but through substitutions
--     lemma-sub : Δ ⊆ Δ′ → ←■ Δ ⇉ Γ → ←■ Δ′ ⇉ Γ
--     lemma-sub ⊆-empty     sub = sub
--     lemma-sub (⊆-drop wk) sub = lemma-sub wk sub
--     lemma-sub (⊆-keep wk) sub = lemma-sub wk sub
--     lemma-sub (⊆-lock wk) sub = {!  !}

-- --     lemma-, = is∷-■,

-- open lemmas

-- -- Much like before. This gives us a substitution that...
-- -- ... only works left of a lock, from one produced by unbox.
-- -- Γ   is   (Γ₁) ■ ∷ Γ₂
-- -- ↓         ↓↓
-- -- Δ   is   (Δ₁) ■ ∷ Γ₂
-- sub-←■ : Δ is Δ₁ ■ ∷ Δ₂ → Γ ⇉ Δ → (←■ Γ) ⇉ Δ₁
-- sub-←■ ext σ = {!   !}

-- -- sub-←■ : Γ is Γ₁ ■ ∷ Γ₂ → Sub Γ Δ → Sub Γ₁ (←■ Δ)
-- -- sub-←■ ext sub with is∷-Δsub ext sub
-- -- ... | ext₂ = {!   !}
-- -- sub-←■ ext sub with is∷-Δsub ext sub
-- -- sub-←■ ext₁          (sub-trim sub wk) | ext₂        = lemma-sub wk (sub-←■ ext₁ sub)
-- -- sub-←■ is-nil        (sub-lock sub)    | _           = sub
-- -- sub-←■ (is-ext ext₁) (sub-keep sub)    | is-ext ext₂ = sub-←■ ext₁ sub
-- -- sub-←■ (is-ext ext₁) (sub-subs sub t)  | ext₂        = sub-←■ ext₁ sub

-- -- Parallel substitution!
-- sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A
-- sub σ (nat x) = nat x
-- -------------------------
-- sub p       (var Z)     = var (S Z)
-- sub (σ • t) (var Z)     = t
-- sub σ       (var (S x)) = sub (p ◦ σ) (var x)
-- ---------------------------------------
-- sub σ (ƛ t)   = ƛ sub (σ+ σ) t
-- sub σ (box t) = box (sub (σ •■) t)
-- sub σ (l ∙ r) = sub σ l ∙ sub σ r
-- -------------------------------------------------
-- sub σ (unbox {ext = e} t) = unbox {ext = is∷-Δsub e σ} (sub (sub-←■ e σ) t)
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

-- -- private variable
-- --     x y     : _ ∈ _
-- --     t t₁ t₂ : _ ⊢ _


-- -- infix 5 _[_]
-- -- -- Single variable substitution on the first free variable.
-- -- -- Used for β-reduction... obviously.
-- -- _[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
-- -- t₁ [ t₂ ] = sub (sub-subs sub-refl t₂) t₁

-- -- -- infix 5 _[_/_]′
-- -- -- -- Single variable substitution, from the above.
-- -- -- _[_/_]′ : Γ ⊢ A → (Γ₁ ∷ Γ₂) ⊢ B → Γ is Γ₁ , B ∷ Γ₂ → (Γ₁ ∷ Γ₂) ⊢ A
-- -- -- t₁ [ t₂ / is-nil ]′   = t₁ [ t₂ ] 
-- -- -- t₁ [ t₂ / is-ext x ]′ = sub (sub-keep (build-sub x (sub-subs sub-refl {!   !}))) t₁ 
-- -- --     where
-- -- --     build-sub : Γ is Γ₁ , A ∷ Γ₂ → Sub (Γ₁ , A) Γ₁ → Sub Γ (Γ₁ ∷ Γ₂)
-- -- --     build-sub (is-ext ext) sub = sub-keep (build-sub ext sub)
-- -- --     build-sub is-nil       sub = sub

-- -- -- Some lemmas about substitution.
-- -- private module lemmas′ where
-- --     -- We need this lemma to prove the below
-- --     ⊆-refl-id : (x : A ∈ Γ) → Γ-weak ⊆-refl x ≡ x
-- --     ⊆-refl-id {Γ = Γ , B} (S x) rewrite ⊆-refl-id x = refl
-- --     ⊆-refl-id {Γ = Γ , B} Z                         = refl

-- -- open lemmas′

-- -- -- Γ , A ⊢ sub (sub-keep (sub-subs sub-refl a₁)) b₁ ~ sub (sub-keep (sub-subs sub-refl a₂)) b₂ ∶ B
-- -- -- 
-- -- -- sub-keep-ƛ : () ≡ 

-- -- -- sub-ƛ : {t₁ : Γ , A ⊢ B} → (ƛ t₁) [ t₂ ] ≡ ƛ (t₁ [ t₂ ])
-- -- -- sub-ƛ {t₁ = t₁} {t₂ = t₂} = {! !}

-- -- -- Substitution with sub-refl doesn't do anything - special case for variables.
-- -- -- Probably true in general, but the case for unbox is annoying.
-- -- -- We don't need it so this is way easier to prove.
-- -- sub-refl-id-var : (t : Γ ⊢ A) → t ≡ var x → sub sub-refl t ≡ t
-- -- sub-refl-id-var (var Z)     refl = refl
-- -- sub-refl-id-var (var (S x)) refl 
-- --     rewrite sub-refl-id-var (var x) refl | ⊆-refl-id x = refl
             
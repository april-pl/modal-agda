module LFExt where
open import Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (_×_) renaming (_,_ to _،_)
open import Data.Sum

private variable
    A B : Type
    Γ Γ′ Γ′′ Δ Δ₁ Δ₂ Γ₁ Γ₂ Γ₃ : Context

infix 3 _is_∷_
-- Lock free extension relation
-- Relates contexts extended to the right with lock free contexts
data _is_∷_ : Context → Context → Context → Set where
    is-nil : Γ is Γ  ∷ ∅
    is-ext : Γ is Γ₁ ∷ Γ₂ → Γ , A is Γ₁ ∷ Γ₂ , A 

-- A barrage of syntactic lemmas relating to locks
-- Not all of these are still used

-- Lock free extensions are equivalences
is∷-≡ : Γ is Γ₁ ∷ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂)
is∷-≡ is-nil                         = refl
is∷-≡ (is-ext ext) rewrite is∷-≡ ext = refl

-- Lock free extensions are equivalences, inverse direction with lock-freeness
≡-is∷ : ¬■ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂) → Γ is Γ₁ ∷ Γ₂
≡-is∷ {Γ₂ = ∅}      prf       refl = is-nil
≡-is∷ {Γ₂ = Γ₂ , x} (¬■, prf) refl = is-ext (≡-is∷ prf refl)

-- Γ is Γ₁ if Γ₂ is empty
is∷-Γ₂≡∅ : Γ is Γ₁ ∷ ∅ → Γ ≡ Γ₁
is∷-Γ₂≡∅ is-nil = refl

-- Left-of-lock is Γ₁ if it ends with a lock
is∷-←■ : Γ is Γ₁ ■ ∷ Γ₂ → (←■ Γ) ≡ Γ₁
is∷-←■ (is-ext ext) = is∷-←■ ext
is∷-←■ is-nil       = refl

is∷-unpeelₗ : Γ ■ is Γ₁ ■ ∷ Γ₂ → Γ ≡ Γ₁
is∷-unpeelₗ is-nil = refl

is∷-unpeelᵣ : Γ ■ is Γ₁ ■ ∷ Γ₂ → Γ₂ ≡ ∅
is∷-unpeelᵣ is-nil = refl

-- Lock free extensions mean lock free contexts.
is∷-¬■Γ : Γ is Γ₁ ∷ Γ₂ → ¬■ Γ₂
is∷-¬■Γ is-nil       = ¬■∅
is∷-¬■Γ (is-ext ext) = ¬■, (is∷-¬■Γ ext)

-- Contexts with locks in aren't lock free.
¬■-■ : ¬■ Γ → ¬ (Γ is Γ₁ ■ ∷ Γ₂)
¬■-■ (¬■, prf) (is-ext ext) = ¬■-■ prf ext

-- If a subcontext has a lock so does the subcontext
-- ■⊆ : Γ ⊆ Δ → Γ is Γ₁ ■ ∷ Γ₂ → Σ[ Δ₂ ∈ Context ] Δ is Γ₁ ■ ∷ Δ₂
-- ■⊆ (⊆-drop {A = A} wk) is-nil with ■⊆ wk is-nil
-- ... | Δ₂ ، ext = Δ₂ , A ، is-ext ext 
-- ■⊆ (⊆-drop {A = A} wk) (is-ext ext) with ■⊆ wk (is-ext ext) 
-- ... | Δ₂ ، ex′ = Δ₂ , A ، is-ext ex′
-- ■⊆ (⊆-keep wk)        (is-ext ext) = ■⊆ (⊆-drop wk) ext
-- ■⊆ (⊆-lock {Δ = Δ} wk) is-nil      = {!   !} ، {!   !}

-- If supercontext of context with a lock, the context also has a lock.
■⊆′ : Γ ■ ⊆ Δ → Σ[ Δ₁ ∈ Context ] Σ[ Δ₂ ∈ Context ] Δ is Δ₁ ■ ∷ Δ₂
■⊆′ {_} {(Δ ■)}   (⊆-lock wk) = Δ ، ∅ ، is-nil
■⊆′ {_} {(Δ , B)} (⊆-drop wk) with ■⊆′ wk
... | Δ₁ ، Δ₂ ، ext = Δ₁ ، Δ₂ , B ، is-ext ext

-- Extensions are congruent under the left-of-lock operation ←■
is∷-←■weak : Γ is Γ₁ ■ ∷ Γ₂ → Γ ⊆ Δ → Γ₁ ⊆ ←■ Δ
is∷-←■weak ext          (⊆-drop wk) = is∷-←■weak ext wk
is∷-←■weak (is-ext ext) (⊆-keep wk) = is∷-←■weak ext wk
is∷-←■weak is-nil       (⊆-lock wk) = wk

-- Apply a weakening to an entire extension
is∷-Δweak : Γ is Γ₁ ■ ∷ Γ₂ → Γ ⊆ Δ → Δ is ((←■ Δ) ■) ∷ (■→ Δ)
is∷-Δweak ext          (⊆-drop wk) = is-ext (is∷-Δweak ext wk)
is∷-Δweak (is-ext ext) (⊆-keep wk) = is-ext (is∷-Δweak ext wk)
is∷-Δweak is-nil       (⊆-lock wk) = is-nil

-- Peel off one layer of locks from a context 
partition : (Γ : Context) → ( Σ[ Γ₁ ∈ Context ] Σ[ Γ₂ ∈ Context ] Γ is Γ₁ ■ ∷ Γ₂ ) ⊎ (¬■ Γ) 
partition ∅     = inj₂ ¬■∅
partition (Γ ■) = inj₁ (Γ ، ∅ ، is-nil)
partition (Γ , A) with partition Γ
... | inj₁ (Γ₁ ، Γ₂ ، ext) = inj₁ (Γ₁ ، Γ₂ , A ، is-ext ext)
... | inj₂ p               = inj₂ (¬■, p)

-- Locked implies a partition
partition-locked : has-■ Γ → Γ is (←■ Γ) ■ ∷ (■→ Γ)
partition-locked {Γ = Γ , x} (,-has-■ p) = is-ext (partition-locked p)
partition-locked {Γ = Γ ■}   ■-has-■     = is-nil

-- Partioned then locked
is∷-locked : Γ is Γ₁ ■ ∷ Γ₂ → has-■ Γ
is∷-locked is-nil       = ■-has-■
is∷-locked (is-ext ext) = ,-has-■ (is∷-locked ext) 

is∷-¬¬■ : Γ is Γ₁ ■ ∷ Γ₂ → ¬ ¬■ Γ
is∷-¬¬■ is-nil       () 
is∷-¬¬■ (is-ext ext) (¬■, p) = is∷-¬¬■ ext p

is∷-≡■-is∷ : Γ is Γ₁ ■ ∷ Γ₂ → Γ is Γ₁ ■ ∷ Γ₃ → Γ₂ ≡ Γ₃
is∷-≡■-is∷ is-nil       is-nil = refl 
is∷-≡■-is∷ (is-ext exl) (is-ext exr) with is∷-≡■-is∷ exl exr
... | refl = refl
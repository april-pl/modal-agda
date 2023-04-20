module LFExt where
open import Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ Γ₃ : Context

infix 3 _is_∷_
-- Lock free extension relation
-- Relates contexts extended to the right with lock free contexts
data _is_∷_ : Context → Context → Context → Set where
    is-nil : Γ is Γ  ∷ ∅
    is-ext : Γ is Γ₁ ∷ Γ₂ → Γ , A is Γ₁ ∷ Γ₂ , A 

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

-- Lock free extensions mean lock free contexts.
is∷-¬■Γ : Γ is Γ₁ ∷ Γ₂ → ¬■ Γ₂
is∷-¬■Γ is-nil       = ¬■∅
is∷-¬■Γ (is-ext ext) = ¬■, (is∷-¬■Γ ext)

-- Contexts with locks in aren't lock free.
¬■-■ : ¬■ Γ → ¬ (Γ is Γ₁ ■ ∷ Γ₂)
¬■-■ (¬■, prf) (is-ext ext) = ¬■-■ prf ext

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
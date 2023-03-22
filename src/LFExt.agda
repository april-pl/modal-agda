module LFExt where
open import Base
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _⸲_)

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ Γ₃ : Context

infix 3 _is_∷_
-- Lock free extension relation
-- Relates contexts extended to the right with lock free contexts
-- Maybe need to formulate this for non-lock free contexts for other calculi
data _is_∷_ : Context → Context → Context → Set where
    is-nil : Γ is Γ  ∷ ∅
    is-ext : Γ is Γ₁ ∷ Γ₂ → Γ , A is Γ₁ ∷ Γ₂ , A 

-- Lock free extensions are equivalences
is∷-≡ : Γ is Γ₁ ∷ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂)
is∷-≡ is-nil                         = refl
is∷-≡ (is-ext ext) rewrite is∷-≡ ext = refl

-- Some syntactic lemmas for extensions of certain forms
-- Most of these are really annoying and only used once :(

-- Lock free extensions are equivalences, inverse direction with lock-freeness
≡-is∷ : ¬■ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂) → Γ is Γ₁ ∷ Γ₂
≡-is∷ {Γ₂ = ∅}      prf       refl = is-nil
≡-is∷ {Γ₂ = Γ₂ , x} (¬■, prf) refl = is-ext (≡-is∷ prf refl)

-- Γ is Γ₁ if Γ₂ is empty
is∷-Γ₂≡∅ : Γ is Γ₁ ∷ ∅ → Γ ≡ Γ₁
is∷-Γ₂≡∅ is-nil = refl

-- Left-of-lock is Γ₁ if it ends with a lock
is∷-←■ : Γ is Γ₁ ■ ∷ Γ₂ → ←■ Γ ≡ Γ₁
is∷-←■ (is-ext ext) = is∷-←■ ext
is∷-←■ is-nil       = refl

-- Lock free is lock free, obviously
is∷-¬■Γ : Γ is Γ₁ ∷ Γ₂ → ¬■ Γ₂
is∷-¬■Γ is-nil       = ¬■∅
is∷-¬■Γ (is-ext ext) = ¬■, (is∷-¬■Γ ext)

-- Contexts with locks in aren't lock free (sunglasses!)
¬■-■ : ¬■ Γ → Γ is Γ₁ ■ ∷ Γ₂ → ⊥
¬■-■ (¬■, prf) (is-ext ext) = ¬■-■ prf ext

-- Match on a context that has an inclusion
is∷-∈ : A ∈ Γ → Σ[ Γ₁ ∈ Context ] Σ[ Γ₂ ∈ Context ] Γ is Γ₁ , A ∷ Γ₂
is∷-∈ {Γ = Γ′ , A} Z = Γ′ ⸲ ∅ ⸲ is-nil
is∷-∈ {Γ = Γ′ , B} (S x) with is∷-∈ x
... | Γ₁ ⸲ ∅        ⸲ is-nil     = Γ₁ ⸲ (∅ , B)      ⸲ is-ext is-nil
... | Γ₁ ⸲ (Γ₂ , C) ⸲ is-ext ext = Γ₁ ⸲ (Γ₂ , C , B) ⸲ is-ext (is-ext ext)

-- Match on a context that ends in cons.
is∷-■, : Γ , A is Γ₁ ■ ∷ Γ₂ → Σ[ Γ₃ ∈ Context ] Γ₂ ≡ Γ₃ , A
is∷-■, {Γ₂ = Γ₂ , x} (is-ext ext) = Γ₂ ⸲ refl

-- Syntax for extension when Γ ends with a lock
is∷-Γ■ : Γ ■ is Γ₁ ∷ Γ₂ → (Γ ■ ≡ Γ₁) × (Γ₂ ≡ ∅)
is∷-Γ■ ext = is∷-Γ■-≡ ext ⸲ is∷-Γ■-∅ ext
    where
    is∷-Γ■-∅ : Γ ■ is Γ₁ ∷ Γ₂ → Γ₂ ≡ ∅ 
    is∷-Γ■-∅ {Γ₂ = ∅} ex = refl
    
    is∷-Γ■-≡ : Γ ■ is Γ₁ ∷ Γ₂ → Γ ■ ≡ Γ₁ 
    is∷-Γ■-≡ {Γ₁ = Γ₁} ext with is∷-Γ■-∅ ext 
    ... | refl = is∷-Γ₂≡∅ ext

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

-- Left congruence for extensions
-- If Γ = Γ₁, Γ₂ then Δ, Γ = Δ, Γ₁, Γ₂
is∷-lcong : Γ is Γ₁ ∷ Γ₂ → (Δ ∷ Γ) is (Δ ∷ Γ₁) ∷ Γ₂
is∷-lcong (is-ext ext) = is-ext (is∷-lcong ext) 
is∷-lcong is-nil       = is-nil       
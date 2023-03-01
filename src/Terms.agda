module Terms where
open import Base
open import Data.Nat 
open import Data.Unit
open import Data.Empty
open import Data.Bool

F : Bool → Set
F b = T (not b)

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ : Context

infixl 6 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ     → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A

    ƛ_    : Γ , A ⊢ B   → Γ   ⊢ A ⇒ B
    box   : Γ ■   ⊢ A   → Γ   ⊢ □ A
    -- Morally, this reads something like 
    -- unbox : Γ     ⊢ □ A → Γ ■ ⊢ A
    -- However we have to deal with weakening etc
    unbox : {ext : Γ is Γ₁ ■ ∷ Γ₂} → Γ₁ ⊢ □ A → Γ ⊢ A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
weakening wk (nat n) = nat n
weakening wk (var x) = var (Γ-weak wk x)
weakening wk (l ∙ r) = (weakening wk l) ∙ (weakening wk r)
weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
weakening wk (box t) = box (weakening (⊆-lock wk) t)
weakening wk (unbox {ext = e} t) 
    = unbox {ext = is∷-Δweak e wk} (weakening (is∷-←■weak e wk) t)


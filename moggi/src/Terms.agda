module Terms where
open import Base
open import Data.Nat 
open import Data.Unit
open import Data.Empty
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)

private variable
    A B T U : Type
    Γ Δ Γ₁ Γ₂ : Context

infixl 6 _∙_
infix  5 ƛ_
infix  5 η_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    zer   : Γ ⊢ Nat
    suc   : Γ ⊢ Nat → Γ ⊢ Nat
    
    var   : A ∈ Γ → Γ ⊢ A

    η_    : Γ ⊢ A     → Γ ⊢ M A 
    ƛ_    : Γ , A ⊢ B → Γ ⊢ A ⇒ B

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    bind_of_ : Γ ⊢ M A → Γ , A ⊢ M B → Γ ⊢ M B


-- weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
-- weakening wk (nat n) = nat n
-- weakening wk (var x) = var (Γ-weak wk x)
-- weakening wk (l ∙ r) = (weakening wk l) ∙ (weakening wk r)
-- weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
-- weakening wk (box t) = box (weakening (⊆-lock wk) t)
-- weakening wk (unbox {ext = e} t) 
--     = unbox {ext = is∷-Δweak e wk} (weakening (is∷-←■weak e wk) t)
 
weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
weakening wk zer     = zer
weakening wk (suc n) = suc (weakening wk n)
weakening wk (var x) = var (Γ-weak wk x)
weakening wk (η t)   = η weakening wk t
weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
weakening wk (l ∙ r) = weakening wk l ∙ weakening wk r
weakening wk (bind t of u) 
    = bind (weakening wk t) of (weakening (⊆-keep wk) u) 
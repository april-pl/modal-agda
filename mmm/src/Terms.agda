module Terms where
open import Base
open import Data.Nat

private variable
    A B : Type
    Γ Δ Γ₁ Γ₂ : Context

infixl 6 _∙_
infix  5 ƛ_
infix  5 η_
infix  3 _⊢_
infix  5 bind_inside_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ         → Γ ⊢ Nat
    var   : A ∈ Γ     → Γ ⊢ A
    ƛ_    : Γ , A ⊢ B → Γ ⊢ A ⇒ B
    η_    : Γ ⊢ A     → Γ ⊢ T A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    
    -- `in` is a reserved keyword.
    bind_inside_ : Γ ⊢ T A → Γ , A ⊢ T B → Γ ⊢ T B

infix 5 bnd
pattern bnd a t = bind a inside t
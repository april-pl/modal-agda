module Calculus where
open import Data.Nat 

infixr 7 _⇒_
-- Modal type constructors.
data Type : Set where
    Nat  : Type
    □_   : Type → Type
    _⇒_ : Type → Type → Type

infixl 5 _,_
-- Contexts with locks.
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
    _■  : Context → Context

-- infixl 6 _;_
-- _;_ : Context → Context → Context
-- a ; b = ?

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x
Γ ∷ Δ ■   = (Γ ∷ Δ) ■

variable
    A B T : Type
    Γ Γ₁ Γ₂ Δ : Context

infix  4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type -> Context -> Set where
    Z  : A ∈ Γ , A
    S_ : A ∈ Γ → A ∈ Γ , B

infixl 7 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A
    ƛ_    : Γ , A ⊢ B → Γ ⊢ A ⇒ B
    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    box   : Γ ■ ⊢ A → Γ ⊢ □ A
    unbox : Γ₁ ⊢ □ A → Γ₁ ■ ∷ Γ₂ ⊢ A
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

private variable
    A B T U : Type
    Γ Γ₁ Γ₂ : Context

infix  4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type -> Context -> Set where
    Z  : A ∈ Γ , A
    S_ : A ∈ Γ → A ∈ Γ , B
    -- L_ : A ∈ Γ → A ∈ Γ ■

-- -- Witnesses the membership of a lock in the context.
-- -- I would like it if this partitioned it!!
-- data Lock : Context -> Set where
--     ZL  : Lock (Γ ■)
--     SL_ : Lock Γ → Lock (Γ , A) 

infixl 6 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ     → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A

    ƛ_    : Γ , A ⊢ B   → Γ   ⊢ A ⇒ B
    box   : Γ ■   ⊢ A   → Γ   ⊢ □ A
    unbox : Γ     ⊢ □ A → Γ ■ ⊢ A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B


-- Well-typed substitution.
-- _[_/_] : ∀ {Γ : Context} {A B : Type} 
--        → Γ , B ⊢ A
--        → Γ     ⊢ B
--        → B ∈ Γ , B
--        -----------
--        → Γ ⊢ A
-- -- nat n [ t₂ / x ] = nat n
-- _[_/_] {Γ} {A} {B} t₁ (var x) (S y) = {!   !}
-- _[_/_] {Γ} {A} {B} t₁ (var x) y = {!  !}
-- _[_/_] {Γ} {□ A} {B} a@(box t₁) t₂ x = {!   !}
-- _[_/_] (l ∙ r) t x = (l [ t / x ]) ∙ (r [ t / x ])
-- _[_/_] _ _ = {!   !} 
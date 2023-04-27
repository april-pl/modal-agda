module Base where
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)

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

private variable
    A B : Type
    Γ Γ′ Δ Δ′ Γ₁ Γ₂ Γ₃ : Context

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x
Γ ∷ Δ ■   = (Γ ∷ Δ) ■

-- Lock-free contexts
data ¬■ : Context → Set where
    ¬■∅ : ¬■ ∅
    ¬■, : ¬■ Γ → ¬■ (Γ , A)

infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z : A ∈ Γ , A
    S : A ∈ Γ → A ∈ Γ , B

-- Nothing can be a member of an empty context
¬A∈∅ : ¬ (A ∈ ∅)
¬A∈∅ ()

-- Elements left of the leftmost lock
←■ : Context → Context
←■ ∅       = ∅
←■ (Γ , A) = ←■ Γ
←■ (Γ ■)   = Γ

-- Elements right of the rightmost lock
■→ : Context → Context
■→ ∅       = ∅
■→ (Γ , A) = ■→ Γ , A
■→ (Γ ■)   = ∅

infix 4 _⊆_
-- Subcontexts, for weakening
data _⊆_ : Context → Context → Set where
    ⊆-empty :         ∅     ⊆ ∅
    ⊆-drop  : Γ ⊆ Δ → Γ     ⊆ Δ , A
    ⊆-keep  : Γ ⊆ Δ → Γ , A ⊆ Δ , A
    ⊆-lock  : Γ ⊆ Δ → Γ ■   ⊆ Δ ■

⊆∅ : Γ ⊆ ∅ → Γ ≡ ∅
⊆∅ {∅} wk = refl
⊆∅ {Γ , x} ()
⊆∅ {Γ ■}   ()

⊆-assoc : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-assoc ⊆-empty wk₂               = wk₂
⊆-assoc (⊆-drop wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-drop wk₁) wk₂)
⊆-assoc (⊆-drop wk₁) (⊆-keep wk₂) = ⊆-drop (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-keep wk₁) wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-keep wk₂) = ⊆-keep (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-lock wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-lock wk₁) wk₂)
⊆-assoc (⊆-lock wk₁) (⊆-lock wk₂) = ⊆-lock (⊆-assoc wk₁ wk₂)

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = Γ , x} = ⊆-keep ⊆-refl
⊆-refl {Γ = Γ ■}   = ⊆-lock ⊆-refl
⊆-refl {Γ = ∅}     = ⊆-empty

⊆-←■ : Γ ⊆ Δ → ←■ Γ ⊆ ←■ Δ
⊆-←■ ⊆-empty     = ⊆-empty
⊆-←■ (⊆-drop wk) = ⊆-←■ wk
⊆-←■ (⊆-keep wk) = ⊆-←■ wk
⊆-←■ (⊆-lock wk) = wk

Γ-weak : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ 
Γ-weak (⊆-drop rest) x     = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) (S x) = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) Z     = Z 
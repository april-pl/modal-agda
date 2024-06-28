module Base where
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)
open import Data.Sum
infixr 7 _⇒_

-- infixl 2 T_
-- Modal type constructors.
data Type : Set where 
    Nat  : Type
    M    : Type → Type
    _⇒_ : Type → Type → Type

infixl 5 _,_
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

private variable
    A B : Type
    Γ Γ′ Δ Δ′ Γ₁ Γ₂ Γ₃ : Context

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x


infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z : A ∈ Γ , A
    S : A ∈ Γ → A ∈ Γ , B

-- Nothing can be a member of an empty context
¬A∈∅ : ¬ (A ∈ ∅)
¬A∈∅ ()

infix 4 _⊆_
-- Subcontexts, for weakening
data _⊆_ : Context → Context → Set where
    ⊆-empty :         ∅     ⊆ ∅
    ⊆-drop  : Γ ⊆ Δ → Γ     ⊆ Δ , A
    ⊆-keep  : Γ ⊆ Δ → Γ , A ⊆ Δ , A

⊆-wk : Γ , A ⊆ Δ → Γ ⊆ Δ
⊆-wk (⊆-drop s) = ⊆-drop (⊆-wk s)
⊆-wk (⊆-keep s) = ⊆-drop s 

⊆∅ : Γ ⊆ ∅ → Γ ≡ ∅
⊆∅ {∅} wk = refl
⊆∅ {Γ , x} ()

⊆-assoc : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-assoc ⊆-empty wk₂               = wk₂
⊆-assoc (⊆-drop wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-drop wk₁) wk₂)
⊆-assoc (⊆-drop wk₁) (⊆-keep wk₂) = ⊆-drop (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-keep wk₁) wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-keep wk₂) = ⊆-keep (⊆-assoc wk₁ wk₂)

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = Γ , x} = ⊆-keep ⊆-refl
⊆-refl {Γ = ∅}     = ⊆-empty

Γ-weak : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ 
Γ-weak (⊆-drop rest) x     = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) (S x) = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) Z     = Z  
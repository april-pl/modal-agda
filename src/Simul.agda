module Simul where
open import Calculus
open import Data.Bool renaming (T to Tr)
open import Function

Fl : Bool -> Set
Fl = Tr ∘ not

variable
    t₁ t₂ a b c x : Γ ⊢ T

locked? : Context → Bool
locked? ∅       = true
locked? (Γ , x) = locked? Γ
locked? (Γ ■)   = false

data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    simLock : {Tr (locked? Γ)} → Γ ⊢ x ~ x ∶ A
    -- simVar  : {Fl (locked? Δ)} → (Γ , A ∷ Δ) ⊢ var ~ var ∶ A
module Simul where
open import Calculus
open import Data.Bool renaming (T to Tr)
open import Function

Fl : Bool -> Set
Fl = Tr ∘ not

locked? : Context → Bool
locked? ∅       = false
locked? (Γ , x) = locked? Γ
locked? (Γ ■)   = true

private variable
    t t' t₁ t₂ t₁' t₂' : _ ⊢ _
    A B T U : Type
    Γ Γ₁ Γ₂ : Context

infix 2 _⊢_~_∶_
data _⊢_~_∶_ : (Γ : Context) → Γ ⊢ A → Γ ⊢ A → (A : Type) → Set where
    simLock : (t  : Γ ⊢ A) 
            → (t' : Γ ⊢ A)
            → {Tr (locked? Γ)}
            ------------------
            → Γ ⊢ t ~ t' ∶ A

    simVar : {Fl (locked? Γ₂)} 
           → {x : A ∈ (Γ₁ , A ∷ Γ₂)}
           ---------------------------------
           → Γ₁ , A ∷ Γ₂ ⊢ var x ~ var x ∶ A

    simApp : Γ ⊢ t₁      ~ t₁'       ∶ A ⇒ B
           → Γ ⊢ t₂      ~ t₂'       ∶ A
           ----------------------------------
           → Γ ⊢ t₁ ∙ t₂ ~ t₁' ∙ t₂' ∶ B

    simLam : Γ , A ⊢ t   ~ t'   ∶ B
           ---------------------------------
           → Γ     ⊢ ƛ t ~ ƛ t' ∶ A ⇒ B

    simBox : Γ ■ ⊢ t     ~ t'     ∶ A
           ----------------------------
           → Γ   ⊢ box t ~ box t' ∶ □ A
    
    simUnbox : Γ₁   ⊢ t       ~ t'       ∶ □ A
             --------------------------------------
             → Γ₁ ■ ⊢ unbox t ~ unbox t' ∶ A  
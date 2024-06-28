module Trans where
open import Base
open import Terms
open import Subst
open import LFExt

private variable
    t  l  r  t₁  t₂  : _ ⊢ _
    t′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context
    □ext : Γ is Γ₁ ■ ∷ Γ₂

infix 4 _→β_
-- Transitiion relation.
data _→β_ : Γ ⊢ A → Γ ⊢ A → Set where
    β■ : unbox {ext = □ext} (box t) →β t
    βƛ : (ƛ t) ∙ r                  →β t [ r ]
    
    ξappl : l →β l′ → l ∙ r →β l′ ∙ r
    ξappr : r →β r′ → l ∙ r →β l  ∙ r′

    -- No β under boxes, we should treat boxes as values.
    -- Otherwise box 1 ~ box ((λx. x) 1), and NI is broken. 
    -- ξbox   : t →β t′ → box   t →β box   t′
    ξunbox : t →β t′ → unbox {ext = □ext} t →β unbox {ext = □ext} t′

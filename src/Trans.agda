module Trans where
open import Calculus
open import Subst

private variable
    t  l  r  t₁  t₂  : _ ⊢ _
    t′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

infix 4 _→β_
-- Transitiion relation.
data _→β_ : Γ ⊢ A → Γ ⊢ A → Set where
    β■ : box (unbox t) →β t
    βƛ : (ƛ t) ∙ r     →β t [ r ]
    
    ξappl : l →β l′ → l ∙ r →β l′ ∙ r
    ξappr : r →β r′ → l ∙ r →β l  ∙ r′

    ξbox   : t →β t′ → box   t →β box   t′
    ξunbox : t →β t′ → unbox t →β unbox t′


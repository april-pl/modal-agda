module Trans where
open import Base
open import Terms
open import Subst

private variable
    t  u  l  r  t₁  t₂  : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

infix 4 _→β_
-- Transitiion relation.
data _→β_ : Γ ⊢ A → Γ ⊢ A → Set where
    βbind : bind (η t) of u →β u [ t ]
    βƛ    : (ƛ t) ∙ r       →β t [ r ]
    
    ξbind : t →β t′ → bind t of u →β bind t′ of u 
    ξappl : l →β l′ → l ∙ r       →β l′ ∙ r
    ξappr : r →β r′ → l ∙ r       →β l  ∙ r′



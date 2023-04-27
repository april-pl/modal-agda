module Trans where
open import Base
open import Terms
open import Subst

private variable
    t  l  r  t₁  t₂  a  : _ ⊢ _
    t′ l′ r′ t₁′ t₂′ a′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

infix 4 _→β_
-- Transitiion relation.
data _→β_ : Γ ⊢ A → Γ ⊢ A → Set where
    βƛ : (ƛ t) ∙ r              →β t [ r ]
    βbind : bind (η a) inside t →β t [ a ] 

    ξappl : l →β l′ → l ∙ r →β l′ ∙ r
    ξappr : r →β r′ → l ∙ r →β l  ∙ r′

    ξbind : a →β a′ 
        → bind a inside t →β bind a′ inside t
module Trans where
open import Base
open import Terms
open import Subst

private variable
    t  u  l  r  t₁  t₂  v : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

infix 4 _↝_
-- Transitiion relation.
data _↝_ : Γ ⊢ A → Γ ⊢ A → Set where
    βbind : bind (η t) of u ↝ u [ t ]
    βƛ    : (ƛ t) ∙ r       ↝ t [ r ]
    
    ξlamd : t ↝ t′ → ƛ t         ↝ ƛ t′
    ξbind : t ↝ t′ → bind t of u ↝ bind t′ of u 
    ξappl : l ↝ l′ → l ∙ r       ↝ l′ ∙ r

-- RTC
data _↝⋆_ : Γ ⊢ A → Γ ⊢ A → Set where
    ⋆refl :                    t ↝⋆ t
    ⋆step : t ↝  u          → t ↝⋆ u
    ⋆trns : t ↝⋆ u → u ↝ v → t ↝⋆ v
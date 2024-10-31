module Trans where
open import Base
open import Terms
open import Subst
open import LFExt

private variable
    t  u  v  l  r  t₁  t₂  : _ ⊢ _
    t′ u′ v′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context
    ext : Γ is Γ₁ ■ ∷ Γ₂

infix 4 _↝_
-- Transitiion relation.
data _↝_ : Γ ⊢ A → Γ ⊢ A → Set where
    β■ : unbox {ext = ext} (box t) ↝ t
    βƛ : (ƛ t) ∙ r                  ↝ t [ r ]
    
    ξsucc : t ↝ t′ → suc t       ↝ suc t′
    ξappl : l ↝ l′ → l ∙ r ↝ l′ ∙ r

    -- No β under boxes, we should treat boxes as values.
    -- Otherwise box 1 ~ box ((λx. x) 1), and NI is broken. 
    -- ξbox   : t ↝ t′ → box   t ↝ box   t′
    ξunbox : t ↝ t′ → unbox {ext = ext} t ↝ unbox {ext = ext} t′

infix 4 _↝⋆_
data _↝⋆_ : Γ ⊢ A → Γ ⊢ A → Set where
    ⋆refl :                    t ↝⋆ t
    ⋆step : t ↝  u          → t ↝⋆ u
    ⋆trns : t ↝⋆ u → u ↝ v → t ↝⋆ v
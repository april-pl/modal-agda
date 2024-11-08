module Trans where
open import Base
open import Terms
open import Subst

private variable
    t  u  l  r  t₁  t₂  v : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context
    θ : TyContext

infix 4 _↝_
-- Transitiion relation.
data _↝_ : Γ ⊢ A → Γ ⊢ A → Set where
    βbind : bind (η t) of u ↝ u [ t ]
    βƛ    : (ƛ t) ∙ r       ↝ t [ r ]

    βinl : case (inl t) of l , r ↝ l [ t ]  
    βinr : case (inr t) of l , r ↝ r [ t ]

    βπ₁ : π₁ ⟨ t , u ⟩ ↝ t
    βπ₂ : π₂ ⟨ t , u ⟩ ↝ u

    βunfold : { B : TypeIn (new none)}
            → { t : Γ ⊢ B ⁅ Rec B ⁆ } 
            → _↝_ { A = B ⁅ Rec B ⁆ } (unfold B (fold B t)) t

    ξsucc : t ↝ t′ → suc t       ↝ suc t′
    ξbind : t ↝ t′ → bind t of u ↝ bind t′ of u 
    ξappl : l ↝ l′ → l ∙ r       ↝ l′ ∙ r
    
    ξcase : t ↝ t′ → case t of l , r ↝ case t′ of l , r
    -- ξinl  : {B : Type} → t ↝ t′ → inl {B = B} t ↝ inl {B = B} t′
    -- ξinr  : {A : Type} → t ↝ t′ → inr {A = A} t ↝ inr {A = A} t′

    ξπ₁ : t ↝ t′ → π₁ t ↝ π₁ t′
    ξπ₂ : t ↝ t′ → π₂ t ↝ π₂ t′

    ξunfold : { B : TypeIn (new none)}
            → { t t′ : Γ ⊢ Rec B }
            → t ↝ t′
            → _↝_  { A = B ⁅ Rec B ⁆ } (unfold B t) (unfold B t′)

-- RTC
infix 4 _↝⋆_
data _↝⋆_ : Γ ⊢ A → Γ ⊢ A → Set where
    ⋆refl :                    t ↝⋆ t
    ⋆step : t ↝  u          → t ↝⋆ u
    ⋆trns : t ↝⋆ u → u ↝ v → t ↝⋆ v
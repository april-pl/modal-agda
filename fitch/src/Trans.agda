module Trans where
open import Base
open import Terms
open import Subst
open import LFExt

open import Relation.Binary.PropositionalEquality hiding ([_])

private variable
    t  u  v  l  r  t₁  t₂  : _ ⊢ _
    t′ u′ v′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B C : Type
    Γ Γ₁ Γ₂ : Context
    ext : Γ is Γ₁ ■ ∷ Γ₂

infix 4 _↝_
-- Transitiion relation.
data _↝_ : Γ ⊢ A → Γ ⊢ A → Set where
    β■ : unbox {ext = ext} (box t) ↝ t
    βƛ : (ƛ t) ∙ r                  ↝ t [ r ]

    βinl : case (inl t) of l , r ↝ l [ t ]  
    βinr : case (inr t) of l , r ↝ r [ t ]

    βπ₁ : π₁ ⟨ t , u ⟩ ↝ t
    βπ₂ : π₂ ⟨ t , u ⟩ ↝ u

    βunfold : { B : TypeIn (new none)}
            → { t : Γ ⊢ B ⁅ Rec B ⁆ } 
            → _↝_ { A = B ⁅ Rec B ⁆ } (unfold B refl (fold B t)) t
    
    ξappl : l ↝ l′ → l ∙ r ↝ l′ ∙ r

    -- No β under boxes, we should treat boxes as values.
    -- Otherwise box 1 ~ box ((λx. x) 1), and NI is broken. 
    -- ξbox   : t ↝ t′ → box   t ↝ box   t′
    ξunbox : t ↝ t′ → unbox {ext = ext} t ↝ unbox {ext = ext} t′

    ξcase : t ↝ t′ → case t of l , r ↝ case t′ of l , r

    ξπ₁ : t ↝ t′ → π₁ t ↝ π₁ t′
    ξπ₂ : t ↝ t′ → π₂ t ↝ π₂ t′

    ξunfold : { B : TypeIn (new none)}
            → { t t′ : Γ ⊢ Rec B }
            → t ↝ t′
            → (p : C ≡ B ⁅ Rec B ⁆)
            → _↝_  { A = C } (unfold B p t) (unfold B p t′)

infix 4 _↝⋆_
data _↝⋆_ : Γ ⊢ A → Γ ⊢ A → Set where
    ⋆refl :                    t ↝⋆ t
    ⋆step : t ↝  u          → t ↝⋆ u
    ⋆trns : t ↝⋆ u → u ↝ v → t ↝⋆ v
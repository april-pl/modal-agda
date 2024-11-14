module Trans where
open import Base
open import Terms
open import Subst

open import Relation.Binary.PropositionalEquality hiding ([_])

private variable
    t  u  l  r  t₁  t₂  v : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B C : Type
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
            → _↝_ { A = B ⁅ Rec B ⁆ } (unfold B refl (fold B t)) t

    ξbind : t ↝ t′ → bind t of u ↝ bind t′ of u 
    ξappl : l ↝ l′ → l ∙ r       ↝ l′ ∙ r
    
    ξcase : t ↝ t′ → case t of l , r ↝ case t′ of l , r

    ξπ₁ : t ↝ t′ → π₁ t ↝ π₁ t′
    ξπ₂ : t ↝ t′ → π₂ t ↝ π₂ t′

    ξunfold : { B : TypeIn (new none)}
            → { t t′ : Γ ⊢ Rec B }
            → t ↝ t′
            → (p : C ≡ B ⁅ Rec B ⁆)
            → _↝_  { A = C } (unfold B p t) (unfold B p t′)

-- RTC
infix 4 _↝⋆_
data _↝⋆_ : Γ ⊢ A → Γ ⊢ A → Set where
    ⋆refl :                    t ↝⋆ t
    ⋆step : t ↝  u          → t ↝⋆ u
    ⋆trns : t ↝⋆ u → u ↝ v → t ↝⋆ v
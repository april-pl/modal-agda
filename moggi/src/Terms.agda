module Terms where
open import Base
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product hiding (_×_) renaming (_,_ to _،_)

private variable
    A B C U : Type
    Γ Δ Γ₁ Γ₂ : Context
    θ : TyContext

infixl 6 _∙_
infix  5 ƛ_
infix  5 η_
infix  5 case_of_,_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    ⋆ : Γ ⊢ Unit
    
    var   : A ∈ Γ → Γ ⊢ A

    η_    : Γ ⊢ A     → Γ ⊢ T A 
    ƛ_    : Γ , A ⊢ B → Γ ⊢ A ⇒ B

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    bind_of_ : Γ ⊢ T A → Γ , A ⊢ T B → Γ ⊢ T B

    case_of_,_ : Γ ⊢ A + B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
    inl : Γ ⊢ A → Γ ⊢ A + B
    inr : Γ ⊢ B → Γ ⊢ A + B

    ⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
    π₁ : Γ ⊢ A × B → Γ ⊢ A
    π₂ : Γ ⊢ A × B → Γ ⊢ B

    fold   : (A : TypeIn (new none)) → Γ ⊢ (A ⁅ Rec A ⁆) → Γ ⊢ Rec A
    unfold : (A : TypeIn (new none)) → (B ≡ A ⁅ Rec A ⁆) → Γ ⊢ Rec A → Γ ⊢ B
    

weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
weakening wk ⋆       = ⋆
weakening wk (var x) = var (Γ-weak wk x)
weakening wk (η t)   = η weakening wk t
weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
weakening wk (l ∙ r) = weakening wk l ∙ weakening wk r
weakening wk (bind t of u) 
    = bind (weakening wk t) of (weakening (⊆-keep wk) u) 
weakening wk (inl t) = inl (weakening wk t)
weakening wk (inr t) = inr (weakening wk t)
weakening wk (case t of l , r) 
    = case weakening wk t of weakening (⊆-keep wk) l , weakening (⊆-keep wk) r
weakening wk ⟨ t , t₁ ⟩ = ⟨ weakening wk t , weakening wk t₁ ⟩
weakening wk (π₁ t)     = π₁ (weakening wk t)
weakening wk (π₂ t)     = π₂ (weakening wk t) 
weakening wk (fold A t)   = fold A (weakening wk t)
weakening wk (unfold A p t) = unfold A p (weakening wk t)
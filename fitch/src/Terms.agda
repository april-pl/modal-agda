module Terms where
open import Base
open import LFExt
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (_×_) renaming (_,_ to _،_)

private variable
    A B C T U : Type
    Γ Δ Γ₁ Γ₂ : Context

infixl 6 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    zer   : Γ ⊢ Nat
    suc   : Γ ⊢ Nat → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A

    ƛ_    : Γ , A ⊢ B   → Γ   ⊢ A ⇒ B
    box   : Γ ■   ⊢ A   → Γ   ⊢ □ A
    -- Ideally, this reads something like 
    -- unbox : Γ     ⊢ □ A → Γ ■ ⊢ A
    -- However we have to deal with weakening etc
    unbox : {ext : Γ is Γ₁ ■ ∷ Γ₂} → Γ₁ ⊢ □ A → Γ ⊢ A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    case_of_,_ : Γ ⊢ A + B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C
    inl : Γ ⊢ A → Γ ⊢ A + B
    inr : Γ ⊢ B → Γ ⊢ A + B

    ⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
    π₁ : Γ ⊢ A × B → Γ ⊢ A
    π₂ : Γ ⊢ A × B → Γ ⊢ B

    fold   : (A : TypeIn (new none)) → Γ ⊢ (A ⁅ Rec A ⁆) → Γ ⊢ Rec A
    unfold : (A : TypeIn (new none)) → (B ≡ A ⁅ Rec A ⁆) → Γ ⊢ Rec A → Γ ⊢ B


weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
weakening wk zer     = zer
weakening wk (suc n) = suc (weakening wk n)
weakening wk (var x) = var (Γ-weak wk x)
weakening wk (l ∙ r) = (weakening wk l) ∙ (weakening wk r)
weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
weakening wk (box t) = box (weakening (⊆-lock wk) t)
weakening wk (unbox {ext = e} t) 
    = unbox {ext = is∷-Δweak e wk} (weakening (is∷-←■weak e wk) t)
weakening wk (inl t) = inl (weakening wk t)
weakening wk (inr t) = inr (weakening wk t)
weakening wk (case t of l , r) 
    = case weakening wk t of weakening (⊆-keep wk) l , weakening (⊆-keep wk) r
weakening wk ⟨ t , t₁ ⟩ = ⟨ weakening wk t , weakening wk t₁ ⟩
weakening wk (π₁ t)     = π₁ (weakening wk t)
weakening wk (π₂ t)     = π₂ (weakening wk t) 
weakening wk (fold A t)   = fold A (weakening wk t)
weakening wk (unfold A p t) = unfold A p (weakening wk t)
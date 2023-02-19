module Subst where
open import Calculus
open import Simul
open import Relation.Binary.PropositionalEquality
open import Data.Bool

private variable
    A B : Type
    Γ Γ₁ Γ₂ : Context

-- Extension lemma, for when we go 'under' binders.
ext : Γ₁ ⊆■ Γ₂ → Γ₁ , B ⊆■ Γ₂ , B
ext ρ Z■      =  Z■
ext ρ (S■ x)  =  S■ (ρ x)

-- Extension lemma, for when we go under boxes!
ext■ : Γ₁ ⊆■ Γ₂ → Γ₁ ■ ⊆■ Γ₂ ■
ext■ ρ (L■ x) = L■ ρ x

-- And the inverse.
■ext : Γ₁ ■ ⊆■ Γ₂ ■ → Γ₁ ⊆■ Γ₂
■ext ρ x with ρ (L■ x)
... | L■ x = x

-- -- Commute renamings and boxes
-- ext-■ : ∀ {Γ₁ Γ₂} → (∀ {A} → A ∈ Γ₁ ■ → A ∈ Γ₂ ■) → (∀ {A} → A ∈ Γ₁ → A ∈ Γ₂)
-- ext-■ {Γ , A} {∅} ρ Z = {!  !}
-- ext-■ {Γ , A} {Γ₂ , x} ρ Z = {!   !}
-- ext-■ {Γ , A} {Γ₂ ■} ρ Z = {!   !}
-- ext-■ ρ (S x) = ext-■ (λ ()) x

-- This probably already exists, somewhere...

-- Apply a renaming to a well-typed term.
ren : Γ₁ ⊆■ Γ₂ → (∀ {A} → Γ₁ ⊢ A  → Γ₂ ⊢ A )
ren ρ (nat n)   = nat n
ren ρ (var x)   = var (∈-str {prf = {!   !}} (ρ (∈-weak x)))
ren ρ (ƛ t)     = ƛ (ren (ext ρ) t)
ren ρ (box t)   = box (ren (ext■ ρ) t)
ren ρ (l ∙ r)   = ren ρ l ∙ ren ρ r   
ren {Γ₁ = Con} ρ (unbox t) = {!   !}
-- ren {Γ₂ = Γ₂ ■} ρ (unbox t)   = unbox (ren (■ext ρ) t)
-- ren {Γ₂ = Γ₂ , B} x (unbox t) = {! !}
-- ren {Γ₂ = ∅} x (unbox t)  = {! !}


-- Extension, but for terms..!
ext′ : (∀ {A}   → A ∈■ Γ₁     →     Γ₂ ⊢ A)
     --------------------------------------
     → (∀ {A B} → A ∈■ Γ₁ , B → Γ₂ , B ⊢ A)
ext′ σ Z■      =  var Z
ext′ σ (S■ x)  =  ren S■_ (σ x)

-- Again, now for boxes.
ext■′ : (∀ {A} → A ∈■ Γ₁   → Γ₂ ⊢ A)
      ----------------------------------
      → (∀ {A} → A ∈■ Γ₁ ■ → Γ₂ ■ ⊢ A)
ext■′ σ (L■ Z■) = {!   !}
ext■′ σ (L■ (S■ a)) = {!   !}
ext■′ σ (L■ (L■ a)) = {!   !}


sub : (∀ {A}  → A ∈■ Γ₁   → Γ₂ ⊢ A)
    ------------------------------- 
    → (∀ {A}  → Γ₁ ⊢ A    → Γ₂ ⊢ A)
sub σ (nat n)   = nat n
sub σ (var x)   = {!   !}
sub σ (ƛ t)     = ƛ sub (ext′ σ) t
sub σ (box t)   = box (sub {!   !} t)
sub σ (l ∙ r)   = sub σ l ∙ sub σ r 
sub σ (unbox t) = sub σ {!   !}
module Subst where
open import Calculus
open import Simul
open import Relation.Binary.PropositionalEquality

-- -- Evidence can only come from variables, not locks or empty contexts.
-- ∈-,-only : ∀ {Γ Γ' A B} → A ∈ Γ → Γ ≡ (Γ' , B)
-- ∈-,-only {∅} ()
-- ∈-,-only {Γ ■} ()
-- ∈-,-only {Γ , A} Z = {!   !}
-- ∈-,-only {Γ , A} (S x) rewrite ∈-,-only x = {!   !}
 
-- Extension lemma, for when we go 'under' binders.
ext : ∀ {Γ₁ Γ₂} → (∀ {A} → A ∈ Γ₁ → A ∈ Γ₂) → (∀ {A B} → A ∈ Γ₁ , B → A ∈ Γ₂ , B)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

-- -- Commute renamings and boxes
-- ext-■ : ∀ {Γ₁ Γ₂} → (∀ {A} → A ∈ Γ₁ ■ → A ∈ Γ₂ ■) → (∀ {A} → A ∈ Γ₁ → A ∈ Γ₂)
-- ext-■ {Γ , A} {∅} ρ Z = {!  !}
-- ext-■ {Γ , A} {Γ₂ , x} ρ Z = {!   !}
-- ext-■ {Γ , A} {Γ₂ ■} ρ Z = {!   !}
-- ext-■ ρ (S x) = ext-■ (λ ()) x

-- Apply a renaming to a well-typed term.
ren : ∀ {Γ₁ Γ₂} 
       → (∀ {A} → A ∈ Γ₁ → A ∈ Γ₂)
       --------------------------- 
       → (∀ {A} → Γ₁ ⊢ A → Γ₂ ⊢ A)
ren ρ (nat n)   = nat n
ren ρ (var x)   = var (ρ x)
ren ρ (ƛ t)     = ƛ (ren (ext ρ) t)
ren ρ (box t)   = {!   !}
ren ρ (l ∙ r)   = ren ρ l ∙ ren ρ r   
ren {Γ₂ = Γ₂ , B} x (unbox t) = {!   !}
ren {Γ₂ = Γ₂ ■} ρ (unbox t)   = unbox (ren {!   !} t)
ren {Γ₂ = ∅} x (unbox t)      = {! 1  !}


-- Extension, but for terms..!
extT : ∀ {Γ₁ Γ₂}
  → (∀ {A}   → A ∈ Γ₁     →     Γ₂ ⊢ A)
  -------------------------------------
  → (∀ {A B} → A ∈ Γ₁ , B → Γ₂ , B ⊢ A)
extT σ Z      =  var Z
extT σ (S x)  =  ren S_ (σ x)


sub : ∀ {Γ₁ Γ₂} 
      → (∀ {A} → A ∈ Γ₁ → Γ₂ ⊢ A)
      --------------------------- 
      → (∀ {A} → Γ₁ ⊢ A → Γ₂ ⊢ A)
sub σ (nat n)   = nat n
sub σ (var x)   = σ x
sub σ (ƛ t)     = ƛ sub (extT σ) t
sub σ (box t)   = box (sub {!   !} t)
sub σ (l ∙ r)   = sub σ l ∙ sub σ r 
sub σ (unbox (var x)) = {!   !}
sub σ (unbox (box t)) = sub σ t
sub σ (unbox (unbox t)) = {!   !}
sub σ (unbox (t ∙ t₁)) = {!   !}
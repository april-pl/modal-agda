module Subst where
open import Base
open import Terms

private variable
    A B : Type
    Γ Δ θ Γ₁ Γ₂ Γ′ Δ₁ Δ₂ Δ′ : Context

infixr 3 _⇉_
infixr 4 _•_

data _⇉_ : Context → Context → Set where
    -- Base substitution
    ε : Γ ⇉ ∅

    -- Weaken a substitution
    wk  : Γ ⊆ Γ′        → Γ′ ⇉ Γ 
    -- Extend a substitution with a term
    _•_ : Γ ⇉ Δ → Γ ⊢ A → Γ ⇉ Δ , A

p : Γ , A ⇉ Γ
p = wk (⊆-drop ⊆-refl)

-- Strengthen the domain of a substitution
⇉-st : Γ ⇉ Δ → Δ′ ⊆ Δ → Γ ⇉ Δ′
⇉-st _       ⊆-empty    = ε
⇉-st (wk x)  w          = wk (⊆-assoc w x)
⇉-st (σ • x) (⊆-drop w) = ⇉-st σ w
⇉-st (σ • x) (⊆-keep w) = ⇉-st σ w • x

⇉-refl : Γ ⇉ Γ
⇉-refl {∅}     = ε
⇉-refl {Γ , x} = p • var Z

{-# TERMINATING #-}
mutual
    _◦_ : Δ ⇉ θ → Γ ⇉ Δ → Γ ⇉ θ
    sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A

    σ+  : Γ ⇉ Δ → Γ , A ⇉ Δ , A
    σ+ σ = (σ ◦ p) • (var Z)

    -- Parallel substitution, defined mutually recursively with composition
    sub σ (nat x) = nat x
    ---------------------
    sub (wk w)  (var Z)     = var (Γ-weak w Z)
    sub (σ • t) (var Z)     = t
    sub σ       (var (S x)) = sub (p ◦ σ) (var x)
    ---------------------------------------------
    sub σ (ƛ t) = ƛ sub (σ+ σ) t
    sub σ (η t) = η sub σ t
    sub σ (l ∙ r) = sub σ l ∙ sub σ r
    ---------------------------------
    sub σ (bind a inside t) = bind (sub σ a) inside (sub (σ+ σ) t)

    ε       ◦ τ = ε
    wk w    ◦ τ = ⇉-st τ w
    (σ • t) ◦ τ         = (σ ◦ τ) • sub τ t

sub-refl : Γ ⇉ Γ
sub-refl {∅}     = ε
sub-refl {Γ , x} = σ+ sub-refl

infix 5 _[_]
-- Single variable substitution on the first free variable. Used in β.
_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
t₁ [ t₂ ] = sub (sub-refl • t₂) t₁
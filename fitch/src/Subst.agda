module Subst where
open import Base
open import Terms
open import LFExt
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (_×_) renaming (_,_ to _،_)
open import Data.Sum

private variable
    A B : Type
    Γ Δ θ Γ₁ Γ₂ Γ′ Δ₁ Δ₂ Δ′ : Context

infixr 3 _⇉_
infixr 4 _•■
infixr 4 _•_

data _⇉_ : Context → Context → Set where
    -- Base substitution
    ε : Δ ⇉ ∅

    -- Extend a substitution with a term
    _•_ : Δ ⇉ Γ → Δ ⊢ A → Δ ⇉ Γ , A
    -- Under locks, with a weakening
    _•[_]■ : Δ₁ ⇉ Γ → Δ is Δ₁ ■ ∷ Δ₂ → Δ ⇉ Γ ■ 

-- Under locks, with no weakening
_•■ : Δ ⇉ Γ → Δ ■ ⇉ Γ ■
σ •■ = σ •[ is-nil ]■

-- Weakening substitutions
wk : Δ ⇉ Γ → Δ , A ⇉ Γ
wk ε           = ε
wk (σ • t)     = wk σ • weakening (⊆-drop ⊆-refl) t
wk (σ •[ w ]■) = σ •[ is-ext w ]■

-- Identity substitution
id : Γ ⇉ Γ
id {(∅)}     = ε
id {Γ , x} = wk id • var Z
id {Γ ■}   = id •[ is-nil ]■

p : Γ , A ⇉ Γ
p = wk id

σ+  : Γ ⇉ Δ → Γ , A ⇉ Δ , A
σ+ σ = wk σ • var Z

-- Contexts in substitutions have the same number of locks
⇉-has-■-l : Δ ⇉ Γ → has-■ Γ → has-■ Δ
⇉-has-■-l (σ • x)     (,-has-■ p) = ⇉-has-■-l σ p
⇉-has-■-l (σ •[ w ]■) p           = is∷-locked w

-- ...which means that this is valid
sub-←■ : Δ ⇉ Γ → ←■ Δ ⇉ ←■ Γ
sub-←■ ε                            = ε
sub-←■ (σ • t)                      = sub-←■ σ
sub-←■ (σ •[ w ]■) rewrite is∷-←■ w = σ

-- thanks to https://github.com/nachivpn/k/src/IK/Term/Base.agda

-- ←■ that computes with substitutions
leftContext : Γ is Γ₁ ■ ∷ Γ₂ → Δ ⇉ Γ → Context
leftContext is-nil       (_•[_]■ {Δ₁ = Δ₁} σ w) = Δ₁
leftContext (is-ext ext) (σ • t)                = leftContext ext σ

rightContext : Γ is Γ₁ ■ ∷ Γ₂ → Δ ⇉ Γ → Context
rightContext is-nil       (_•[_]■ {Δ₂ = Δ₂} σ w) = Δ₂
rightContext (is-ext ext) (σ • t)                = rightContext ext σ

-- Properly push a substitution under a context in a way that computes
factor : (ext : Γ is Γ₁ ■ ∷ Γ₂) → (σ : Δ ⇉ Γ) → (leftContext ext σ) ⇉ Γ₁
factor is-nil       (σ •[ w ]■) = σ
factor (is-ext ext) (σ • t)     = factor ext σ

factor′ : (ext : Γ is Γ₁ ■ ∷ Γ₂) → (σ : Δ ⇉ Γ) → Δ is (leftContext ext σ) ■ ∷ (rightContext ext σ)
factor′ is-nil       (σ •[ w ]■) = w
factor′ (is-ext ext) (σ • t)     = factor′ ext σ

-- Parallel substitution
sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A
sub σ zer     = zer
sub σ (suc n) = suc (sub σ n)
---------------------
sub (σ • t) (var Z)     = t
sub (σ • t) (var (S x)) = sub σ (var x)
---------------------------------------
sub σ (ƛ t)   = ƛ sub (σ+ σ) t
sub σ (box t) = box (sub (σ •■) t)
sub σ (l ∙ r) = sub σ l ∙ sub σ r
---------------------------------
sub σ (case t of l , r) = case sub σ t of sub (σ+ σ) l , sub (σ+ σ) r
sub σ ⟨ l , r ⟩         = ⟨ sub σ l , sub σ r ⟩
-----------------------------------------------
sub σ (inl t) = inl (sub σ t)
sub σ (inr t) = inr (sub σ t)
sub σ (π₁ t)  = π₁ (sub σ t)
sub σ (π₂ t)  = π₂ (sub σ t)
----------------------------
sub σ (unbox {ext = ext} t) = 
    unbox {ext = factor′ ext σ} (sub (factor ext σ) t)

_◦_ : Δ ⇉ Γ → θ ⇉ Δ → θ ⇉ Γ
ε           ◦ τ = ε
(σ • t)     ◦ τ = (σ ◦ τ) • sub τ t
-----------------------------------
(σ •[ is-ext w ]■) ◦ (τ • t) with sub-←■ τ 
... | τ′                     with is∷-←■ w
... | refl                   with ⇉-has-■-l τ (is∷-locked w)
... | lock = (σ ◦ τ′) •[ partition-locked lock ]■
-------------------------------------------------
(σ •[ w ]■) ◦ (τ •[ m ]■) with is∷-unpeelₗ w
... | refl = (σ ◦ τ) •[ m ]■

infix 5 _[_]
-- Single variable substitution on the first free variable. Used in β.
_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A 
t₁ [ t₂ ] = sub (id • t₂) t₁     
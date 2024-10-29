module Subst where
open import Base
open import Terms
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
infixr 4 _•_

data _⇉_ : Context → Context → Set where
    -- Base substitution
    ε : Δ ⇉ ∅
    -- Extend a substitution with a term
    _•_ : Δ ⇉ Γ → Δ ⊢ A → Δ ⇉ Γ , A

-- Weakening substitutions
wk : Δ ⇉ Γ → Δ , A ⇉ Γ
wk ε           = ε
wk (σ • t)     = wk σ • weakening (⊆-drop ⊆-refl) t

-- Identity substitution
id : Γ ⇉ Γ
id {(∅)}   = ε
id {Γ , x} = wk id • var Z

p : Γ , A ⇉ Γ
p = wk id

σ+  : Γ ⇉ Δ → Γ , A ⇉ Δ , A
σ+ σ = wk σ • var Z

-- _◦_ : Δ ⇉ Γ → θ ⇉ Δ → θ ⇉ Γ
-- ε           ◦ τ = ε
-- (σ • t)     ◦ τ = (σ ◦ τ) • sub τ t
-- -----------------------------------
-- (σ •[ is-ext w ]■) ◦ (τ • t) with sub-←■ τ 
-- ... | τ′                     with is∷-←■ w
-- ... | refl                   with ⇉-has-■-l τ (is∷-locked w)
-- ... | lock = (σ ◦ τ′) •[ partition-locked lock ]■
-- -------------------------------------------------
-- (σ •[ w ]■) ◦ (τ •[ m ]■) with is∷-unpeelₗ w
-- ... | refl = (σ ◦ τ) •[ m ]■

-- Parallel substitution
sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A
sub σ zer     = zer
sub σ (suc n) = suc (sub σ n)
---------------------
sub (σ • t) (var Z)     = t
sub (σ • t) (var (S x)) = sub σ (var x)
---------------------------------------
sub σ (η t)   = η sub σ t
sub σ (l ∙ r) = sub σ l ∙ sub σ r
---------------------------------
sub σ (ƛ t) = ƛ sub (σ+ σ) t
----------------------------
sub σ (bind t of u) = bind (sub σ t) of sub (σ+ σ) u 
----------------------------------------------------
sub σ (case t of l , r) = case sub σ t of sub (σ+ σ) l , sub (σ+ σ) r
sub σ ⟨ l , r ⟩         = ⟨ sub σ l , sub σ r ⟩
-----------------------------------------------
sub σ (inl t) = inl (sub σ t)
sub σ (inr t) = inr (sub σ t)
sub σ (π₁ t)  = π₁ (sub σ t)
sub σ (π₂ t)  = π₂ (sub σ t)

-- Composition of substitutions
_◦_ : Δ ⇉ Γ → θ ⇉ Δ → θ ⇉ Γ
ε       ◦ τ = ε 
(σ • t) ◦ τ = (σ ◦ τ) • sub τ t

infix 5 _[_]
-- Single variable substitution on the first free variable. Used in β.
_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
t [ u ] = sub (id • u) t    
module Subst where
open import Base
open import Terms
open import LFExt
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _،_)
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
id {∅}     = ε
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

-- Parallel substitution
sub : Γ ⇉ Δ → Δ ⊢ A → Γ ⊢ A
sub σ (nat x) = nat x
---------------------
sub (σ • t) (var Z)     = t
sub (σ • t) (var (S x)) = sub σ (var x)
---------------------------------------
sub σ (ƛ t)   = ƛ sub (σ+ σ) t
sub σ (box t) = box (sub (σ •■) t)
sub σ (l ∙ r) = sub σ l ∙ sub σ r
---------------------------------
sub (σ •[ w ]■) (unbox {ext = e} t) with is∷-unpeelₗ e 
... | refl = unbox {ext = w} (sub σ t) 
sub (_•_ {Δ = Δ} {A = B} σ u) (unbox {ext = is-ext e} t) with is∷-←■ e
... | refl = 
        let Γ-locked = is∷-locked e
            Δ-locked = ⇉-has-■-l σ Γ-locked
            Δ-parted = partition-locked Δ-locked
        in unbox {ext = Δ-parted} (sub (sub-←■ σ) t)
    
    -- ε       ◦ τ = ε
    -- wk w    ◦ τ = ⇉-st τ w
    -- (σ • t) ◦ τ         = (σ ◦ τ) • sub τ t
    -- (σ •■)  ◦ wk w with ■⊆′ w | w
    -- ... | Γ₁  ، ∅ ، is-nil     | ⊆-lock w = (σ ◦ wk w) •■
    -- ... | _   ، _ ، is-ext ext | w        = (σ •■) ◦ wk w
    -- (σ •■) ◦ (τ •■) = (σ ◦ τ) •■

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
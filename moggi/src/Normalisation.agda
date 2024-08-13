module Normalisation where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _،_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty 
open import Data.Sum
open import Data.Nat
open import Base
open import Terms
open import Subst
open import Simul
open import Trans

private variable
    t  u  l  r  t₁  t₂  : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

data Value : Γ ⊢ A → Set where
    Vƛ : {t : Γ , B ⊢ A} → Value t → Value (ƛ t)
    Vℕ : {n : ℕ} → Value {Γ = Γ} (nat n)
    Vη : Value (η t)

normal : {Γ : Context} → {A : Type} → (t : Γ ⊢ A) → Set
normal {Γ} {A} t = {t′ : Γ ⊢ A} → ¬ (t ↝ t′)

¬val-var : {x : A ∈ Γ} → ¬ Value (var x) 
¬val-var = λ ()

value-lem : (t : Γ ⊢ A) → Value t ⊎ ¬ (Value t)
value-lem (nat n) = inj₁ Vℕ
value-lem (var x) = inj₂ (λ ())
value-lem (η t)   = inj₁ Vη
value-lem (l ∙ r) = inj₂ (λ ())
value-lem (ƛ t) with value-lem t 
... | inj₁  v = inj₁ (Vƛ v)
... | inj₂ ¬v = inj₂ λ { (Vƛ v) → ¬v v }
value-lem (bind t of u) = inj₂ (λ ())

value-normal : Value t → normal t
value-normal (Vƛ v) (ξlamd step) = value-normal v step
value-normal Vℕ ()
value-normal Vη ()

-- ¬value-step : {t : Γ ⊢ A} → ¬ Value t → Σ[ t′ ∈ Γ ⊢ A ] t ↝ t′
-- ¬value-step {t = t} ¬v = ?

-- normal-value : (t : ∅ ⊢ A) → normal t → Value t
-- normal-value (nat x) p = Vℕ
-- normal-value (η t)   p = Vη
-- normal-value (ƛ t) p with value-lem t 
-- ... | inj₂ ¬v        with ¬value-step ¬v
-- ... | t′ ، step = ⊥-elim (p (ξlamd step))
-- normal-value (ƛ t) p | inj₁  v = Vƛ v

-- normal-value (l     ∙ r)     p with normal-value l (λ s → p (ξappl s))
-- normal-value ((ƛ l) ∙ r)     p | p′ = ⊥-elim (p {t′ = l [ r ]} βƛ)
-- normal-value (bind t   of u) p with normal-value t (λ s → p (ξbind s)) 
-- normal-value (bind η t of u) p | p′ = ⊥-elim (p {t′ = u [ t ]} βbind) 

-- Well-known result, replicating this is besides the point of the project
postulate
    normalising : (t : ∅ ⊢ A) → Σ[ t′ ∈ ∅ ⊢ A ] t ↝⋆ t′ × normal t′

-- Indistinguishability is syntactic equality on values
ind-eql : (t : Γ ⊢ A) → (u : Γ ⊢ A) → pure A → Value t → Value u → Γ ⊢ t ~ u ∶ A  → t ≡ u
ind-eql (nat x) (nat x) p       vt      vu      (sim-nat x)   = refl
ind-eql (η t)   (η u)   p       vt      vu      (sim-mon _ _) = impure p
ind-eql (ƛ t)   (ƛ u)   (p⇒ p) (Vƛ vt) (Vƛ vu) (sim-lam sim) 
    with ind-eql t u p vt vu sim 
... | refl = refl
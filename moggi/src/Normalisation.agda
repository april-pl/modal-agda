module Normalisation where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _،_)
open import Relation.Nullary
open import Data.Empty 
open import Data.Nat
open import Base
open import Terms
open import Subst
open import Simul
open import Trans

private variable
    t  u  l  r  t₁  t₂  u₁  u₂  v₁  v₂  w : _ ⊢ _
    t′ u′ l′ r′ t₁′ t₂′ : _ ⊢ _
    A B : Type
    Γ Γ₁ Γ₂ : Context

data Value : Γ ⊢ A → Set where
    Vƛ : {t : Γ , B ⊢ A} → Value (ƛ t) 
    Vz : Value {Γ = Γ} zer
    Vs : Value t → Value (suc t)
    Vη : Value (η t)

normal : {Γ : Context} → {A : Type} → (t : Γ ⊢ A) → Set
normal {Γ} {A} t = {t′ : Γ ⊢ A} → ¬ (t ↝ t′)

infix 1 _⇓_
_⇓_ : Γ ⊢ A → Γ ⊢ A → Set
t ⇓ v = t ↝⋆ v × normal v

value-normal : Value t → normal t
value-normal Vƛ     = λ ()
value-normal Vη     = λ ()
value-normal Vz     = λ ()
value-normal (Vs v) step with value-normal v
value-normal (Vs v) (ξsucc step) | v′ = v′ step

normal-value : (t : ∅ ⊢ A) → normal t → Value t
normal-value zer p = Vz
normal-value (η t) p = Vη
normal-value (ƛ t) p = Vƛ

normal-value (l     ∙ r)     p with normal-value l (λ s → p (ξappl s))
normal-value ((ƛ l) ∙ r)     p | p′ = ⊥-elim (p {t′ = l [ r ]} βƛ)
normal-value (bind t   of u) p with normal-value t (λ s → p (ξbind s)) 
normal-value (bind η t of u) p | p′ = ⊥-elim (p {t′ = u [ t ]} βbind) 
normal-value (suc n)         p with normal-value n (λ s → p (ξsucc s)) 
normal-value (suc n)         p | a = Vs a

module confluence-proof where
    -- Indexed n-step reduction
    data _↝[_]_ : Γ ⊢ A → ℕ → Γ ⊢ A → Set where
        stepz : t ↝[ 0 ] t
        steps : {n : ℕ} 
              → t ↝[ n ] u 
              → u ↝ w 
              ---------------
              → t ↝[ suc n ] w

    -- Single step determinism
    deterministic : t ↝ u₁ → t ↝ u₂ → u₁ ≡ u₂
    deterministic βbind      βbind      = refl
    deterministic βƛ         βƛ         = refl
    deterministic (ξsucc s₁) (ξsucc s₂) with deterministic s₁ s₂
    ... | refl = refl
    deterministic (ξbind s₁) (ξbind s₂) with deterministic s₁ s₂
    ... | refl = refl
    deterministic (ξappl s₁) (ξappl s₂) with deterministic s₁ s₂
    ... | refl = refl

    -- N-step determinism
    deterministic[] : (n : ℕ) → t ↝[ n ] u₁ → t ↝[ n ] u₂ → u₁ ≡ u₂
    deterministic[] zero stepz stepz = refl
    deterministic[] (suc n) (steps s₁ s₁′) (steps s₂ s₂′) 
               with deterministic[] n s₁ s₂
    ... | refl with deterministic s₁′ s₂′ 
    ... | refl = refl


-- Well-known results, replicating this is besides the point of the project
postulate
    normalising : (t : ∅ ⊢ A) → Σ[ t′ ∈ ∅ ⊢ A ] t ↝⋆ t′ × normal t′
    confluent   : (t : ∅ ⊢ A) → t ⇓ v₁ → t ⇓ v₂ → v₁ ≡ v₂

-- ind-eql : (t : ∅ ⊢ A) → (u : ∅ ⊢ A) → pure A → Value t → Value u → ∅ ⊢ t ~ u ∶ A  → t ≡ u
-- ind-eql (nat x) (nat x) p        vt vu (sim-nat x)   = refl
-- ind-eql (η t)   (η u)   p        vt vu (sim-mon _ _) = impure p
-- ind-eql (ƛ t)   (ƛ u)   (p⇒ p₁) vt vu (sim-lam sim) = {!   !}
-- ... | a = {! sim  !}

-- Indistinguishability is syntactic equality on values
ind-eql : (n : ∅ ⊢ Nat) → (m : ∅ ⊢ Nat) → Value n → Value m → ∅ ⊢ n ~ m ∶ Nat → n ≡ m
ind-eql zer     zer     Vz      Vz      sim-zer       = refl
ind-eql (suc n) (suc m) (Vs vn) (Vs vm) (sim-suc sim) with ind-eql n m vn vm sim
... | refl = refl 

ind-eql′ : {n : ∅ ⊢ Nat} → {m : ∅ ⊢ Nat} → Value n → Value m → ∅ ⊢ n ~ m ∶ Nat → n ≡ m
ind-eql′ {n = n} {m = m} vn vm sim = ind-eql n m vn vm sim 

sim-value : (n : ∅ ⊢ Nat) 
          → (m : ∅ ⊢ Nat)
          → ∅ ⊢ n ~ m ∶ Nat 
          → Value n 
          ---------
          → Value m
sim-value zer zer sim Vz = Vz
sim-value (suc n) (suc m) (sim-suc sim) (Vs vn) with sim-value n m sim vn 
... | v = Vs v
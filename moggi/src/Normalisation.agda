module Normalisation where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product renaming (_,_ to _،_; _×_ to Product)
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

    V× : Value ⟨ t , u ⟩
    Vl : {B : Type} → Value (inl {B = B} t)
    Vr : {A : Type} → Value (inr {A = A} t)

normal : {Γ : Context} → {A : Type} → (t : Γ ⊢ A) → Set
normal {Γ} {A} t = {t′ : Γ ⊢ A} → ¬ (t ↝ t′)

infix 1 _⇓_
_⇓_ : Γ ⊢ A → Γ ⊢ A → Set
t ⇓ v = Product (t ↝⋆ v) (normal v)

value-normal : Value t → normal t
value-normal Vƛ = λ ()
value-normal Vη = λ ()
value-normal Vz = λ ()
value-normal V× = λ ()
value-normal Vl = λ ()
value-normal Vr = λ ()
value-normal (Vs v) step with value-normal v
value-normal (Vs v) (ξsucc step) | v′ = v′ step
 

normal-value : (t : ∅ ⊢ A) → normal t → Value t
normal-value zer p = Vz
normal-value (η t) p = Vη
normal-value (ƛ t) p = Vƛ
normal-value (inl t) p = Vl
normal-value (inr t) p = Vr
normal-value ⟨ l , r ⟩ p = V×

normal-value (l     ∙ r)             p with normal-value l (λ s → p (ξappl s))
normal-value ((ƛ l) ∙ r)             p | p′ = ⊥-elim (p {t′ = l [ r ]} βƛ)
normal-value (bind t   of u)         p with normal-value t (λ s → p (ξbind s)) 
normal-value (bind η t of u)         p | p′ = ⊥-elim (p {t′ = u [ t ]} βbind) 
normal-value (case t of l , r)       p with normal-value t (λ s → p (ξcase s)) 
normal-value (case (inl _) of l , r) p | Vl = ⊥-elim (p βinl)
normal-value (case (inr _) of l , r) p | Vr = ⊥-elim (p βinr)
normal-value (π₁ t)                  p with normal-value t (λ s → p (ξπ₁ s))
normal-value (π₁ ⟨ l , r ⟩)          p | V× = ⊥-elim (p βπ₁)
normal-value (π₂ t)                  p with normal-value t (λ s → p (ξπ₂ s))
normal-value (π₂ ⟨ l , r ⟩)          p | V× = ⊥-elim (p βπ₂)
normal-value (suc n)                 p with normal-value n (λ s → p (ξsucc s)) 
normal-value (suc n)                 p | a = Vs a



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
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
    V⋆ : {Γ : Context} → Value {Γ = Γ} ⋆
    Vη : Value (η t)

    V× : Value ⟨ t , u ⟩
    Vl : {B : Type} → Value t → Value (inl {B = B} t)
    Vr : {A : Type} → Value t → Value (inr {A = A} t)
    Vf : {B : TypeIn (new none)} → {t : Γ ⊢ B ⁅ Rec B ⁆} → Value (fold B t)

infix 1 _⇓_
_⇓_ : Γ ⊢ A → Γ ⊢ A → Set
t ⇓ v = Product (t ↝⋆ v) (Value v)

-- Indistinguishability is syntactic equality on values
-- ind-eql : (n : ∅ ⊢ Nat) → (m : ∅ ⊢ Nat) → Value n → Value m → ∅ ⊢ n ~ m ∶ Nat → n ≡ m
-- ind-eql zer     zer     Vz      Vz      sim-zer       = refl
-- ind-eql (suc n) (suc m) (Vs vn) (Vs vm) (sim-suc sim) with ind-eql n m vn vm sim
-- ... | refl = refl 

ind-eql : (p q : ∅ ⊢ Bool) → Value p → Value q → ∅ ⊢ p ~ q ∶ Bool → p ≡ q
ind-eql (inl ⋆) (inl ⋆) (Vl V⋆) (Vl V⋆) (sim-inl sim) = refl
ind-eql (inr ⋆) (inr ⋆) (Vr V⋆) (Vr V⋆) (sim-inr sim) = refl

ind-eql′ : {p q : ∅ ⊢ Bool} → Value p → Value q → ∅ ⊢ p ~ q ∶ Bool → p ≡ q
ind-eql′ {p = p} {q = q} vp vq sim = ind-eql p q vp vq sim 

sim-value : (p : ∅ ⊢ Bool) 
          → (q : ∅ ⊢ Bool)
          → ∅ ⊢ p ~ q ∶ Bool 
          → Value p 
          ---------
          → Value q
sim-value (inl ⋆) (inl ⋆) (sim-inl sim-one) (Vl V⋆) = Vl V⋆
sim-value (inr ⋆) (inr ⋆) (sim-inr sim-one) (Vr V⋆) = Vr V⋆ 
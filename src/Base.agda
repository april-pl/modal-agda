module Base where
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)

infixr 7 _⇒_
-- Modal type constructors.
data Type : Set where
    Nat  : Type
    □_   : Type → Type
    _⇒_ : Type → Type → Type

_≡?ₜ_ : (A B : Type) → Dec (A ≡ B)
Nat ≡?ₜ Nat = yes refl
Nat ≡?ₜ (□ B) = no λ ()
Nat ≡?ₜ (B ⇒ B₁) = no λ ()
-------------------------
(□ A) ≡?ₜ Nat = no λ ()
(□ A) ≡?ₜ (□ B) with A ≡?ₜ B
... | yes refl = yes refl
... | no ¬refl = no λ{refl → ¬refl refl}
(□ A) ≡?ₜ (B ⇒ B₁) = no λ ()
---------------------------
(A ⇒ A′) ≡?ₜ Nat   = no λ ()
(A ⇒ A′) ≡?ₜ (□ B) = no λ ()
(A ⇒ A′) ≡?ₜ (B ⇒ B′) with A ≡?ₜ B  | A′ ≡?ₜ B′
... | yes refl | yes refl = yes refl
... | no ¬refl | _        = no λ{refl → ¬refl refl}
... | _        | no ¬refl = no λ{refl → ¬refl refl}

infixl 5 _,_
-- Contexts with locks.
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
    _■  : Context → Context

private variable
    A B : Type
    Γ Γ′ Δ Δ′ Γ₁ Γ₂ Γ₃ : Context

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x
Γ ∷ Δ ■   = (Γ ∷ Δ) ■

∷-, : (Γ₁ ∷ Γ₂ , A) ≡ (Γ₁ ∷ Γ₂) , A
∷-, = refl 

-- Lock-free contexts
data ¬■ : Context → Set where
    ¬■∅ : ¬■ ∅
    ¬■, : ¬■ Γ → ¬■ (Γ , A)

infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z : A ∈ Γ , A
    S : A ∈ Γ → A ∈ Γ , B
    -- L : A ∈ Γ → A ∈ Γ ■

-- Variable membership has decidable equality
-- Could extend this to different types?
_≡?ₓ_ : (x y : A ∈ Γ) → Dec (x ≡ y)
_≡?ₓ_ Z    Z      = yes refl
_≡?ₓ_ Z    (S y)  = no (λ ())
_≡?ₓ_ (S x) Z     = no (λ ())
_≡?ₓ_ (S x) (S y) with x ≡?ₓ y
... | yes refl = yes refl
... | no ¬refl = no λ{refl → ¬refl refl}

-- Elements right of an inclusion
∈→ : A ∈ Γ → Context
∈→ Z             = ∅
∈→ (S {B = B} x) = ∈→ x , B
-- ∈→ (L x)         = ∈→ x ■

-- Elements left of an inclusion
←∈ : A ∈ Γ → Context
←∈ {Γ = (Δ , _)} Z     = Δ
←∈ {Γ = (Δ , _)} (S x) = ←∈ {Γ = Δ} x
-- ←∈ {Γ = (Δ ■)  } (L x) = ←∈ {Γ = Δ} x 

-- Elements left of the leftmost lock
←■ : Context → Context
←■ ∅       = ∅
←■ (Γ , A) = ←■ Γ
←■ (Γ ■)   = Γ

-- Elements right of the rightmost lock
■→ : Context → Context
■→ ∅       = ∅
■→ (Γ , x) = ■→ Γ , x
■→ (Γ ■)   = ∅

infix 4 _⊆_
-- Subcontexts, for weakening
data _⊆_ : Context → Context → Set where
    ⊆-empty :         ∅     ⊆ ∅
    ⊆-drop  : Γ ⊆ Δ → Γ     ⊆ Δ , A
    ⊆-keep  : Γ ⊆ Δ → Γ , A ⊆ Δ , A
    ⊆-lock  : Γ ⊆ Δ → Γ ■   ⊆ Δ ■

-- ∅⊆Γ : ∅ ⊆ Γ
-- ∅⊆Γ {∅} = ⊆-empty
-- ∅⊆Γ {Γ , x} = ⊆-drop ∅⊆Γ
-- ∅⊆Γ {Γ ■} = {!   !}

⊆∅ : Γ ⊆ ∅ → Γ ≡ ∅
⊆∅ {∅} wk = refl
⊆∅ {Γ , x} ()
⊆∅ {Γ ■}   ()

-- A stronger version of this exists in LFExt
■⊆ : Γ ■ ⊆ Δ → Σ[ Δ₁ ∈ Context ] Σ[ Δ₂ ∈ Context ] Δ ≡ (Δ₁ ■ ∷ Δ₂)
■⊆ {_} {(Δ ■)}   (⊆-lock wk) = Δ ، ∅ ، refl
■⊆ {_} {(Δ , B)} (⊆-drop wk) with ■⊆ wk
... | Δ₁ ، Δ₂ ، refl = Δ₁ ، Δ₂ , B ، refl

-- ⊆■ : Γ ⊆ Δ ■ → Σ[ Γ′ ∈ Context ] Γ ≡ (Γ′ ■)
-- ⊆■ {(Γ′ ■)} (⊆-lock wk) = Γ′ ، refl
-- ⊆■ {_}      ⊆-empty     = {!   !} ، {!   !}

-- I wrote this entire thing using auto.
⊆-assoc : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-assoc ⊆-empty wk₂               = wk₂
⊆-assoc (⊆-drop wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-drop wk₁) wk₂)
⊆-assoc (⊆-drop wk₁) (⊆-keep wk₂) = ⊆-drop (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-keep wk₁) wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-keep wk₂) = ⊆-keep (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-lock wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-lock wk₁) wk₂)
⊆-assoc (⊆-lock wk₁) (⊆-lock wk₂) = ⊆-lock (⊆-assoc wk₁ wk₂)

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = Γ , x} = ⊆-keep ⊆-refl
⊆-refl {Γ = Γ ■}   = ⊆-lock ⊆-refl
⊆-refl {Γ = ∅}     = ⊆-empty

⊆-←■ : Γ ⊆ Δ → ←■ Γ ⊆ ←■ Δ
⊆-←■ ⊆-empty     = ⊆-empty
⊆-←■ (⊆-drop wk) = ⊆-←■ wk
⊆-←■ (⊆-keep wk) = ⊆-←■ wk
⊆-←■ (⊆-lock wk) = wk

-- private lemma-weak : (Γ : Context) → Γ , A ⊆ Δ → Γ ⊆ Δ
-- lemma-weak ∅ wk = {!   !}
-- lemma-weak (Γ , x) wk = {!   !}
-- lemma-weak (Γ ■) (⊆-drop wk) = lemma-weak {!   !} {! wk!}
-- lemma-weak (Γ ■) (⊆-keep wk) = {!   !}

-- private lemma-⊆,≡ : Γ , A ⊆ Δ , B → A ≡ B
-- lemma-⊆,≡ (⊆-drop wk) = {!   !}
-- lemma-⊆,≡ (⊆-keep wk) = refl

-- _⊆?_ : (Γ Δ : Context) → Dec (Γ ⊆ Δ)
-- ∅ ⊆? ∅ = yes ⊆-empty
-- ∅ ⊆? (Δ , x) with ∅ ⊆? Δ
-- ... | yes why = yes (⊆-drop why)
-- ... | no ¬why = no λ{ (⊆-drop wk) → ¬why wk}
-- ∅ ⊆? (Δ ■) = no λ ()

-- (Γ , x) ⊆? ∅ = no λ ()
-- (Γ , x) ⊆? (Δ , y) with x ≡? y | Γ ⊆? Δ
-- ... | no ¬refl | yes ⊆-empty = no λ{(⊆-keep wk) → ¬refl refl}
-- ... | no ¬refl | yes (⊆-drop why) = no λ{wk → {!   !}}
-- ... | no ¬refl | yes (⊆-keep why) = no λ{wk → {!   !}}
-- ... | no ¬refl | yes (⊆-lock why) = no λ{wk → {!   !}}
-- ... | no ¬refl | no ¬why = {!   !}
-- ... | yes refl | yes why = {!   !}
-- ... | yes refl | no ¬why = no λ{(⊆-drop wk) → ¬why {! !}
--                    ; (⊆-keep wk) → ¬why wk}
-- (Γ , x) ⊆? (Δ ■) = no λ ()

-- (Γ ■) ⊆? ∅ = no λ ()
-- (Γ ■) ⊆? (Δ , x) with Γ ⊆? (←■ Δ)
-- ... | yes why = yes {!    !}
-- ... | no ¬why = {!   !}
-- (Γ ■) ⊆? (Δ ■)   with Γ ⊆? Δ
-- ... | yes why = yes (⊆-lock why)
-- ... | no ¬why = no λ{(⊆-lock wk) → ¬why wk}

Γ-weak : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ 
Γ-weak (⊆-drop rest) x     = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) (S x) = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) Z     = Z 
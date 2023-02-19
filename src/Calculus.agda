module Calculus where
open import Data.Nat 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Bool 

F : Bool → Set
F b = T (not b)

infixr 7 _⇒_
-- Modal type constructors.
data Type : Set where
    Nat  : Type
    □_   : Type → Type
    _⇒_ : Type → Type → Type

infixl 5 _,_
-- Contexts with locks.
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context
    _■  : Context → Context

private variable
    A B : Type
    Γ Γ₁ Γ₂ : Context

-- Evidence that a context contains a lock.
-- data Locked : Context -> Set where
--     Lock : Locked (Γ ■)
--     LExt : Locked Γ → Locked (Γ , A)

-- lock? : (Γ : Context) → Dec (Locked Γ)
-- lock? ∅       = no λ ()
-- lock? (Γ ■)   = yes Lock
-- -- lock? (Γ , x) = map′ LExt (λ { (LExt ctx) → ctx }) (lock? Γ)
-- does  (lock? (Γ , x)) = does (lock? Γ)
-- proof (lock? (Γ , x)) with lock? Γ
-- ... | yes p = ofʸ (LExt p)
-- ... | no ¬p = ofⁿ (λ { (LExt ctx) → ¬p ctx })

-- The good membership, this time
data idk : Context → Type → Set where


-- idk : Context → Type → Bool
-- idk ∅ ty = {!   !}
-- idk (Γ , x) ty = {!   !}
-- idk (Γ ■) ty = {!   !}

lock?ᵇ : Context → Bool
lock?ᵇ ∅       = false
lock?ᵇ (Γ , x) = lock?ᵇ Γ
lock?ᵇ (Γ ■)   = true

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x
Γ ∷ Δ ■   = (Γ ∷ Δ) ■

infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z  : A ∈ Γ , A
    S_ : A ∈ Γ → A ∈ Γ , B

infix 4 _⊆_
_⊆_ : (Γ₁ Γ₂ : Context) → Set
Γ₁ ⊆ Γ₂ = ∀ {A} → A ∈ Γ₁ → A ∈ Γ₂

infix 4 _∈■_
-- As above, but can go under locks.
-- This definition is used for renaming etc.
data _∈■_ : Type → Context → Set where
    Z■  : A ∈■ Γ , A
    S■_ : A ∈■ Γ → A ∈■ Γ , B
    L■_ : A ∈■ Γ → A ∈■ Γ ■

infix 4 _⊆■_
_⊆■_ : (Γ₁ Γ₂ : Context) → Set
Γ₁ ⊆■ Γ₂ = ∀ {A} → A ∈■ Γ₁ → A ∈■ Γ₂

-- Weaken 
∈-weak : A ∈ Γ → A ∈■ Γ 
∈-weak Z     = Z■
∈-weak (S x) = S■ ∈-weak x

-- Strengthen, given a proof of no locks
∈-str : { prf : F (lock?ᵇ Γ) } → A ∈■ Γ → A ∈ Γ
∈-str Z■                 = Z
∈-str {prf = prf} (S■ x) = S ∈-str {prf = prf} x
∈-str {prf = prf} (L■ x) with prf
... | ()

-- ∈-str {Γ} {prf = prf} (S■ x) = S ∈-str {prf = downgrade prf} x
--     where
--     -- Honestly, I'm not even sure what to call this... 
--     downgrade : ∀ {α Δ} → False (lock? (Δ , α)) → False (lock? Δ)
--     downgrade {α} {Δ} prf with toWitnessFalse {Q = lock? (Δ , α)} prf | lock? Δ
--     ... | ¬lock | .true  because ofʸ  p = ⊥-elim (¬lock (LExt p))
--     ... | _     | .false because ofⁿ ¬p = tt
-- ∈-str {Γ} {prf = prf} (L■ x) with toWitnessFalse {Q = lock? Γ} prf
-- ... | ¬lock = ⊥-elim (¬lock Lock)

infixl 6 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ     → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A

    ƛ_    : Γ , A ⊢ B   → Γ   ⊢ A ⇒ B
    box   : Γ ■   ⊢ A   → Γ   ⊢ □ A
    unbox : Γ     ⊢ □ A → Γ ■ ⊢ A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

-- ¬var■ : ∀ {x} → (term : Γ ⊢ A) → term ≡ var x → False (lock? Γ)
-- ¬var■ {x} t refl = {!    !}

-- Well-typed substitution.
-- _[_/_] : ∀ {Γ : Context} {A B : Type} 
--        → Γ , B ⊢ A
--        → Γ     ⊢ B
--        → B ∈ Γ , B
--        -----------
--        → Γ ⊢ A
-- -- nat n [ t₂ / x ] = nat n
-- _[_/_] {Γ} {A} {B} t₁ (var x) (S y) = {!   !}
-- _[_/_] {Γ} {A} {B} t₁ (var x) y = {!  !}
-- _[_/_] {Γ} {□ A} {B} a@(box t₁) t₂ x = {!   !}
-- _[_/_] (l ∙ r) t x = (l [ t / x ]) ∙ (r [ t / x ])
-- _[_/_] _ _ = {!   !}    
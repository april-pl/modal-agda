module Base where
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to Prod)

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
    Γ Δ Γ₁ Γ₂ : Context

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x
Γ ∷ Δ ■   = (Γ ∷ Δ) ■

-- Lock-free contexts
¬■Γ : Context → Set
¬■Γ ∅       = ⊤
¬■Γ (Γ , x) = ¬■Γ Γ
¬■Γ (Γ ■)   = ⊥

-- -- Evidence that a context contains a lock.
-- data Locked : Context -> Set where
--     Lock : Locked (Γ ■)
--     LExt : Locked Γ → Locked (Γ , A)

-- Decidable predicate for if a context is locked.
-- The boolean version seemed to work better?
-- lock? : (Γ : Context) → Dec (Locked Γ)
-- lock? ∅       = no λ ()
-- lock? (Γ ■)   = yes Lock
-- lock? (Γ , x) = map′ LExt (λ { (LExt ctx) → ctx }) (lock? Γ)
-- -- does  (lock? (Γ , x)) = does (lock? Γ)
-- -- proof (lock? (Γ , x)) with lock? Γ
-- -- ... | yes p = ofʸ (LExt p)
-- -- ... | no ¬p = ofⁿ (λ { (LExt ctx) → ¬p ctx })

-- -- Boolean predicate representing if a list is locked or not.
-- lock?ᵇ : Context → Bool
-- lock?ᵇ ∅       = false
-- lock?ᵇ (Γ , x) = lock?ᵇ Γ
-- lock?ᵇ (Γ ■)   = true



infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z : A ∈ Γ , A
    S : A ∈ Γ → A ∈ Γ , B
    -- L : A ∈ Γ → A ∈ Γ ■

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

-- -- Witness a partition of a context around a type.
-- record _is_+_+_ (Γ Γ₁ : Context) (A : Type) (Γ₂ : Context) : Set where
--     constructor _&_ 
--     field
--         is← : {x : A ∈ Γ} → (←∈ x) ≡ (Γ₁ , A)
--         is→ : {x : A ∈ Γ} → (∈→ x) ≡ (Γ₁ , A)

-- -- If given a proof A ∈ Γ, this partitions the context into Γ₁ , A , Γ₂ .
-- ∈× : A ∈ Γ → Σ[ Γ₁ ∈  Context ] Σ[ Γ₂ ∈ Context ] Γ is Γ₁ + A + Γ₂
-- ∈× x = let Γ₁′ = ←∈ x
--            Γ₂′ = ∈→ x 
--        in Γ₁′ ,, Γ₂′ ,, ({! λ {a → ?}  !} & {!   !})

infix 4 _⊆_
-- Subcontexts, for weakening
data _⊆_ : Context → Context → Set where
    ⊆-empty :         ∅     ⊆ ∅
    ⊆-drop  : Γ ⊆ Δ → Γ     ⊆ Δ , A
    ⊆-keep  : Γ ⊆ Δ → Γ , A ⊆ Δ , A
    ⊆-lock  : Γ ⊆ Δ → Γ ■   ⊆ Δ ■

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = Γ , x} = ⊆-keep ⊆-refl
⊆-refl {Γ = Γ ■}   = ⊆-lock ⊆-refl
⊆-refl {Γ = ∅}     = ⊆-empty

Γ-weak : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ 
Γ-weak (⊆-drop rest) x     = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) (S x) = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) Z     = Z

infix 3 _is_∷_
-- Lock free extension relation
-- Relates contexts extended to the right with lock free contexts
-- Maybe need to formulate this for non-lock free contexts for other calculi
data _is_∷_ : Context → Context → Context → Set where
    is-nil : Γ is Γ  ∷ ∅
    is-ext : Γ is Γ₁ ∷ Γ₂ → Γ , A is Γ₁ ∷ Γ₂ , A 

is∷-≡ : Γ is Γ₁ ∷ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂)
is∷-≡ is-nil                         = refl
is∷-≡ (is-ext ext) rewrite is∷-≡ ext = refl

≡-is∷ : ¬■Γ Γ₂ → Γ ≡ (Γ₁ ∷ Γ₂) → Γ is Γ₁ ∷ Γ₂
≡-is∷ {Γ₂ = ∅}      prf refl = is-nil
≡-is∷ {Γ₂ = Γ₂ , x} prf refl = is-ext (≡-is∷ prf refl)

is∷-Γ₂≡∅ : Γ is Γ₁ ∷ ∅ → Γ ≡ Γ₁
is∷-Γ₂≡∅ is-nil = refl

is∷-¬■Γ : Γ is Γ₁ ∷ Γ₂ → ¬■Γ Γ₂
is∷-¬■Γ is-nil       = tt
is∷-¬■Γ (is-ext ext) = is∷-¬■Γ ext

private module lemmas where
    is∷-Γ■-∅ : Γ ■ is Γ₁ ∷ Γ₂ → Γ₂ ≡ ∅ 
    is∷-Γ■-∅ {Γ₂ = ∅} ex = refl
    
    is∷-Γ■-≡ : Γ ■ is Γ₁ ∷ Γ₂ → Γ ■ ≡ Γ₁ 
    is∷-Γ■-≡ {Γ₁ = Γ₁} ext with is∷-Γ■-∅ ext 
    ... | refl = is∷-Γ₂≡∅ ext

open lemmas
is∷-Γ■ : Γ ■ is Γ₁ ∷ Γ₂ → (Γ ■ ≡ Γ₁) × (Γ₂ ≡ ∅)
is∷-Γ■ ext = Prod (is∷-Γ■-≡ ext) (is∷-Γ■-∅ ext)

-- Extensions are congruent under the left-of-lock operation ←■
is∷-←■weak : Γ is Γ₁ ■ ∷ Γ₂ → Γ ⊆ Δ → Γ₁ ⊆ ←■ Δ
is∷-←■weak ext          (⊆-drop wk) = is∷-←■weak ext wk
is∷-←■weak (is-ext ext) (⊆-keep wk) = is∷-←■weak ext wk
is∷-←■weak is-nil       (⊆-lock wk) = wk

-- Apply a weakening to an entire extension
is∷-Δweak : Γ is Γ₁ ■ ∷ Γ₂ → Γ ⊆ Δ → Δ is ((←■ Δ) ■) ∷ (■→ Δ)
is∷-Δweak ext          (⊆-drop wk) = is-ext (is∷-Δweak ext wk)
is∷-Δweak (is-ext ext) (⊆-keep wk) = is-ext (is∷-Δweak ext wk)
is∷-Δweak is-nil       (⊆-lock wk) = is-nil

-- Left congruence for extensions
-- If Γ = Γ₁, Γ₂ then Δ, Γ = Δ, Γ₁, Γ₂
is∷-lcong : Γ is Γ₁ ∷ Γ₂ → (Δ ∷ Γ) is (Δ ∷ Γ₁) ∷ Γ₂
is∷-lcong (is-ext ext) = is-ext (is∷-lcong ext) 
is∷-lcong is-nil       = is-nil
{-# OPTIONS --allow-unsolved-metas #-}

module Terms where
open import Base
open import LFExt
open import Data.Nat 
open import Data.Unit
open import Data.Empty
open import Function.Base
-- open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _،_)

-- F : Bool → Set
-- F b = T (not b)

private variable
    A B T U : Type
    Γ Δ Γ₁ Γ₂ : Context

infixl 6 _∙_
infix  5 ƛ_
infix  3 _⊢_
-- The type of well-typed and scoped terms.
data _⊢_ : Context → Type → Set where
    nat   : ℕ     → Γ ⊢ Nat
    var   : A ∈ Γ → Γ ⊢ A

    ƛ_    : Γ , A ⊢ B   → Γ   ⊢ A ⇒ B
    box   : Γ ■   ⊢ A   → Γ   ⊢ □ A
    -- Ideally, this reads something like 
    -- unbox : Γ     ⊢ □ A → Γ ■ ⊢ A
    -- However we have to deal with weakening etc
    unbox : {ext : Γ is Γ₁ ■ ∷ Γ₂} → Γ₁ ⊢ □ A → Γ ⊢ A

    _∙_   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B


-- map-unbox : (ext : Γ is Γ₁ ■ ∷ Γ₂) 
--           → (t : Γ₁ ⊢ □ A) → (unb : Γ ⊢ A) 
--           → {unb ≡ unbox {ext = ext} t} 
--           → (f : Context → Context)
--           → Σ[ Δ ] Δ is (f Γ₁) ■ ∷ Γ₂ × Δ ⊢ A 
-- map-unbox = {!   !}

-- -- Alternative for unbox that mostly sidesteps the extension issue
-- -- Maybe this should just be the definition?
-- unbox-alt : ■Γ Γ → (←■ Γ) ⊢ □ A → Γ ⊢ A
-- unbox-alt {Γ = Γ , x} prf t with unbox-alt {Γ = Γ} prf (unbox t) 
-- ... | a = unbox {ext = {! is-nil !}} t
-- unbox-alt {Γ = Γ ■}   prf t = unbox {ext = is-nil} t

weakening : Γ ⊆ Δ → Γ ⊢ A → Δ ⊢ A
weakening wk (nat n) = nat n
weakening wk (var x) = var (Γ-weak wk x)
weakening wk (l ∙ r) = (weakening wk l) ∙ (weakening wk r)
weakening wk (ƛ t)   = ƛ weakening (⊆-keep wk) t
weakening wk (box t) = box (weakening (⊆-lock wk) t)
weakening wk (unbox {ext = e} t) 
    = unbox {ext = is∷-Δweak e wk} (weakening (is∷-←■weak e wk) t)

-- private swapped : Γ is Γ₁ , A , B ∷ Γ₂ → Context
-- swapped {Γ} {Γ₁} {A} {B} {Γ₂} _ = (Γ₁ , B , A) ∷ Γ₂

-- private helper : (ext : Γ is Γ₁ , A , B ∷ Γ₂) → swapped ext is Γ₁ , B , A ∷ Γ₂
-- helper is-nil       = is-nil
-- helper (is-ext ext) = is-ext (helper ext)

-- Exchange isn't admissable around locks, but here are some special cases.
-- exchange : Γ is Γ₁ , A , B ∷ Γ₂ → Γ ⊢ T → Σ[ Γ′ ∈ Context ] Γ′ is Γ₁ , B , A ∷ Γ₂ × Γ′ ⊢ T
-- exchange ext (nat x)   = swapped ext ، helper ext ، nat x
-- exchange ext (var x)   = swapped ext ، helper ext ، {!   !}
-- exchange ext (box t)   = swapped ext ، helper ext ، {!   !}
-- exchange ext (unbox t) = swapped ext ، helper ext ، {!   !}
-- exchange ext (l ∙ r)   = swapped ext ، helper ext ، {!  !} ∙ {!   !}
-- exchange {_} {Γ₁} {A} {B} {Γ₂} ext (ƛ_ {A = U} t) rewrite ∷-, {Γ₁ , B , A} {Γ₂} {U} = swapped ext ، helper ext ، ƛ {!    !}



-- The type of exchanges, which swaps two elements in a context.
data Exchange : Context → Context → Set where
    -- xchg-base : Exchange ∅ ∅
    xchg-swap : Exchange (Γ , A , B) (Γ , B , A)
    xchg-keep : Exchange Γ Δ → Exchange (Γ , A) (Δ , A)
    xchg-lock : Exchange Γ Δ → Exchange (Γ ■)   (Δ ■)

xchg-∈ : Exchange Γ Δ → A ∈ Γ → A ∈ Δ
xchg-∈ xchg-swap        Z         = S Z
xchg-∈ xchg-swap        (S Z)     = Z
xchg-∈ xchg-swap        (S (S x)) = S (S x)
xchg-∈ (xchg-keep xchg) Z         = Z
xchg-∈ (xchg-keep xchg) (S x)     = S (xchg-∈ xchg x)
    
exchange : Exchange Γ Δ → Γ ⊢ A → Δ ⊢ A
exchange _    (nat x) = nat x
exchange xchg (l ∙ r) = exchange xchg l ∙ exchange xchg r
exchange xchg (var x) = var (xchg-∈ xchg x)

-- exchange xchg (var x) = {!   !}
exchange xchg-swap (ƛ t)     = ƛ exchange (xchg-keep xchg-swap) t
exchange xchg-swap (box t)   = box (exchange (xchg-lock xchg-swap) t)
exchange xchg-swap (unbox {ext = e} t) = {!   !}
-- ... | ed = unbox {ext = {!   !}} t
--     where
--     lemma : Γ , A , B is Γ₁ ■ ∷ Γ₂ → Σ[ C ∈ Context ] Γ , B , A is Γ₁ ■ ∷ C
--     lemma (is-ext (is-ext is-nil)) = {! Γ₁ !} ، {!   !}
--     lemma (is-ext (is-ext (is-ext ext))) = {!   !} ، {!   !}


exchange (xchg-keep xchg) (ƛ t)     = ƛ exchange (xchg-keep (xchg-keep xchg)) t
exchange (xchg-keep xchg) (box t)   = box (exchange (xchg-lock (xchg-keep xchg)) t)
exchange (xchg-keep xchg) (unbox t) = unbox {ext = {!   !}} t

exchange (xchg-lock xchg) (ƛ t) = ƛ exchange (xchg-keep (xchg-lock xchg)) t
exchange (xchg-lock xchg) (box t) = box (exchange (xchg-lock (xchg-lock xchg)) t)
exchange (xchg-lock xchg) (unbox t) = unbox {ext = {!   !}} t


-- interleaved mutual
--     exchange, : Γ , A , B , U ⊢ T → Γ , B , A , U ⊢ T
--     exchange■ : (Γ , A , B) ■ ⊢ T → (Γ , B , A) ■ ⊢ T
--     exchange  : Γ , A , B     ⊢ T → Γ , B , A     ⊢ T
    
--     exchange, (nat x)   = nat x
--     exchange, (var x)   = {!   !}
--     exchange, (ƛ t)     = {!   !}
--     exchange, (box t)   = box (exchange■ {!   !})
--     exchange, (unbox t) = unbox {!  !}
--     exchange, (l ∙ r)   = exchange, l ∙ exchange, r

--     exchange■ (nat x)   = nat x
--     exchange■ (ƛ t)     = {!   !}
--     exchange■ (box t)   = {!   !}
--     exchange■ (unbox t) = {!   !}
--     exchange■ (l ∙ r)   = exchange■ l ∙ exchange■ r

--     exchange (nat x)   = nat x
--     exchange (var Z)   = var (S Z)
--     exchange (var (S x)) = var {!  !}
--     exchange (ƛ t)     = ƛ exchange, t
--     exchange (l ∙ r)   = exchange l ∙ exchange r
--     exchange (box t)   = box (exchange■ t)
--     exchange (unbox t) = {!   !}    
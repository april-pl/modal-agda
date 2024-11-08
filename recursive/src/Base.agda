module Base where
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product hiding (_×_) renaming (_,_ to _،_)
open import Data.Sum

infixr 7 _⇒_
infixr 7 _×_
infixr 7 _+_

-- Essentially a list of names
data TyContext : Set where
    none :  TyContext
    new  : TyContext → TyContext 

private variable
    θ θ′ : TyContext

data α∈_ : TyContext → Set where
    Zty : α∈ (new θ)
    Sty : α∈ θ → α∈ (new θ)

data TypeIn : TyContext → Set where 
    TyVar : α∈ θ → TypeIn θ

    Nat  : TypeIn θ
    T    : TypeIn θ → TypeIn θ
    _⇒_ : TypeIn θ → TypeIn θ → TypeIn θ
    _×_  : TypeIn θ → TypeIn θ → TypeIn θ
    _+_  : TypeIn θ → TypeIn θ → TypeIn θ  

    Rec : TypeIn (new θ) → TypeIn θ

Type : Set
Type = TypeIn none

ty-weakening : TypeIn θ → TypeIn (new θ)
ty-weakening (TyVar x) = TyVar (Sty x)
ty-weakening (Rec t)   = Rec (ty-weakening t)
ty-weakening (T t)     = T (ty-weakening t)
ty-weakening (l ⇒ r)  = ty-weakening l ⇒ ty-weakening r
ty-weakening (l × r)   = ty-weakening l × ty-weakening r
ty-weakening (l + r)   = ty-weakening l + ty-weakening r
ty-weakening Nat = Nat

data TySub : TyContext → TyContext → Set where
    tnil : TySub θ none
    text : TySub θ′ θ → TypeIn θ′ → TySub θ′ (new θ)

ty-wk : TySub θ′ θ → TySub (new θ′) θ
ty-wk tnil = tnil
ty-wk (text σ t) = text (ty-wk σ) (ty-weakening t)

ty-id : TySub θ θ
ty-id {θ = none} = tnil
ty-id {θ = new θ} = text (ty-wk ty-id) (TyVar Zty)

ty+ : TySub θ′ θ → TySub (new θ′) (new θ)
ty+ σ = text (ty-wk σ) (TyVar Zty)

rep : TySub θ′ θ → TypeIn θ → TypeIn θ′
rep (text σ t) (TyVar Zty)     = t
rep (text σ t) (TyVar (Sty x)) = rep σ (TyVar x)
rep σ (Rec t)                  = Rec (rep (ty+ σ) t)

rep σ (T t)    = T (rep σ t)
rep σ (l ⇒ r) = rep σ l ⇒ rep σ r
rep σ (l × r)  = rep σ l × rep σ r
rep σ (l + r)  = rep σ l + rep σ r
rep σ Nat      = Nat

_⁅_⁆ : TypeIn (new θ) → TypeIn θ → TypeIn θ
t ⁅ τ ⁆ = rep (text ty-id τ) t
 
infixl 5 _,_
data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

private variable
    A B : Type
    Γ Γ′ Δ Δ′ Γ₁ Γ₂ Γ₃ : Context

infixl 4 _∷_
-- -- Context combination.
_∷_ : Context → Context → Context
Γ ∷ ∅     = Γ
Γ ∷ Δ , x = (Γ ∷ Δ) , x

infix 4 _∈_
-- Witnesses the membership of a variable with a given type in a context.
data _∈_ : Type → Context → Set where
    Z : A ∈ Γ , A
    S : A ∈ Γ → A ∈ Γ , B

-- Nothing can be a member of an empty context
¬A∈∅ : ¬ (A ∈ ∅)
¬A∈∅ ()

infix 4 _⊆_
-- Subcontexts, for weakening
data _⊆_ : Context → Context → Set where
    ⊆-empty :         ∅     ⊆ ∅
    ⊆-drop  : Γ ⊆ Δ → Γ     ⊆ Δ , A
    ⊆-keep  : Γ ⊆ Δ → Γ , A ⊆ Δ , A

⊆-wk : Γ , A ⊆ Δ → Γ ⊆ Δ
⊆-wk (⊆-drop s) = ⊆-drop (⊆-wk s)
⊆-wk (⊆-keep s) = ⊆-drop s 

⊆∅ : Γ ⊆ ∅ → Γ ≡ ∅
⊆∅ {(∅)} wk = refl
⊆∅ {Γ , x} ()

⊆-assoc : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-assoc ⊆-empty wk₂               = wk₂
⊆-assoc (⊆-drop wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-drop wk₁) wk₂)
⊆-assoc (⊆-drop wk₁) (⊆-keep wk₂) = ⊆-drop (⊆-assoc wk₁ wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-drop wk₂) = ⊆-drop (⊆-assoc (⊆-keep wk₁) wk₂)
⊆-assoc (⊆-keep wk₁) (⊆-keep wk₂) = ⊆-keep (⊆-assoc wk₁ wk₂)

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = Γ , x} = ⊆-keep ⊆-refl
⊆-refl {Γ = ∅}     = ⊆-empty

Γ-weak : Γ ⊆ Δ → A ∈ Γ → A ∈ Δ 
Γ-weak (⊆-drop rest) x     = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) (S x) = S (Γ-weak rest x)
Γ-weak (⊆-keep rest) Z     = Z  

-- Evidence that a type is pure (non-modal)
data pure : Type → Set where
    pℕ  : pure Nat
    p⇒ : pure B → pure (A ⇒ B)
    p× : pure (A × B)
    p+ : pure (A + B)
 
¬M-pure : ¬ pure (T A)
¬M-pure () 

impure : {P : Set} → pure (T A) → P
impure ()   
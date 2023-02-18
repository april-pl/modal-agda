module Lemmas where
open import Calculus
open import Simul
open import Data.Product

-- Variable weakening. The terms are different, but inhabitants...
-- vweak : Γ₅ ∷ Γ₆ ⊢ T → (Γ₅ , B ∷ Γ₆) ⊢ T
-- vweak (nat n) = nat n
-- vweak (unbox t) = ?
-- vweak (unbox t) = ?
-- vweak t = {!  !} 
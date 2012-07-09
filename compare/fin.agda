module compare.fin where

open import Data.Nat as ℕ hiding (compare)
open import Data.Fin as F hiding (compare)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data ordering {n : ℕ} (i j : Fin n) : Set where
  lt : F.suc i F.≤ (inject₁ j) → ordering i j
  eq : i ≡ j → ordering i j
  gt : F.suc j F.≤ (inject₁ i) → ordering i j

compare : ∀ {n} (i j : Fin n) → ordering i j
compare zero zero = eq refl
compare zero (suc j) = lt (s≤s z≤n)
compare (suc i) zero = gt (s≤s z≤n)
compare (suc i) (suc j) with compare i j
... | lt x = lt (s≤s x)
... | eq x = eq (cong suc x)
... | gt x = gt (s≤s x)

congpred : ∀ {n} {i j : Fin n} (eq : F.suc i ≡ F.suc j) → i ≡ j
congpred refl = refl

eqdec : ∀ {n} (i j : Fin n) → Dec (i ≡ j)
eqdec zero zero = yes refl
eqdec zero (suc j) = no (λ ())
eqdec (suc i) zero = no (λ ())
eqdec (suc i) (suc j) with eqdec i j
... | yes x = yes (cong suc x)
... | no ¬x = no (λ x → ¬x (congpred x))
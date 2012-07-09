module compare.nat where

open import Data.Nat hiding (compare)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data ordering (i j : ℕ) : Set where
  lt : suc i ≤ j → ordering i j
  eq : i ≡ j → ordering i j
  gt : suc j ≤ i → ordering i j

compare : ∀ i j → ordering i j
compare zero zero = eq refl
compare zero (suc j) = lt (s≤s z≤n)
compare (suc i) zero = gt (s≤s z≤n)
compare (suc i) (suc j) with compare i j
... | lt x = lt (s≤s x)
... | eq x = eq (cong suc x)
... | gt x = gt (s≤s x)

eqdec : ∀ (m n : ℕ) → Dec (m ≡ n)
eqdec zero zero = yes refl
eqdec zero (suc n) = no (λ ())
eqdec (suc m) zero = no (λ ())
eqdec (suc m) (suc n) with eqdec m n
... | yes x = yes (cong suc x)
... | no ¬x = no (λ x → ¬x (cong pred x))
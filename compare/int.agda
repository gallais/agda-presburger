module compare.int where

open import Data.Nat as ℕ hiding (compare)
open import Data.Integer as ℤ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

import compare.nat as cℕ
open import integer.order

data ordering (i j : ℤ) : Set where
  lt : ℤ.suc i ℤ.≤ j → ordering i j
  eq : i ≡ j → ordering i j
  gt : ℤ.suc j ℤ.≤ i → ordering i j

compare : ∀ i j → ordering i j
compare -[1+ i ] -[1+ j ] with cℕ.compare i j
... | cℕ.lt x = gt (-< x)
... | cℕ.eq x = eq (cong -[1+_] x)
... | cℕ.gt x = lt (-< x)
compare -[1+ i ] (+ j) = lt (-<+ i j)
compare (+ i) -[1+ j ] = gt (-<+ j i)
compare (+ i) (+ j) with cℕ.compare i j
... | cℕ.lt x = lt (+≤+ x)
... | cℕ.eq x = eq (cong +_ x)
... | cℕ.gt x = gt (+≤+ x)

eqdec : ∀ (i j : ℤ) → Dec (i ≡ j)
eqdec -[1+ i ] -[1+ j ] with cℕ.eqdec i j
... | yes x = yes (cong -[1+_] x)
... | no ¬x = no (λ x → ¬x (cong (λ z → ℕ.pred ∣ z ∣) x))
eqdec -[1+ i ] (+ j) = no (λ ())
eqdec (+ i) -[1+ j ] = no (λ ())
eqdec (+ i) (+ j) with cℕ.eqdec i j
... | yes x = yes (cong +_ x)
... | no ¬x = no (λ x → ¬x (cong ∣_∣ x))
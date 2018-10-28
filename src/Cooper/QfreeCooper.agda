module Cooper.QfreeCooper where

open import Representation
open import Properties
open import Properties-prop
open import Normalization.Negation
open import Cooper.NnfCooper

open import Data.Product as Prod
open import Data.Nat

qelim : ∀ {n f} (φ : QFree {suc n} f) → ∃ (QFree {n})
qelim φ = Prod.map₂ NNF-QFree (Nnf-qelim (proj₂ (nnf φ)))

module Cooper.NnfCooper where

open import Properties
open import Properties-prop
open import Normalization.Linearisation
open import Cooper.LinCooper

open import Data.Nat as ℕ using (ℕ)
open import Data.Product as Prod

Nnf-qelim : ∀ {n f} → NNF {ℕ.suc n} f → ∃ (NNF {n})
Nnf-qelim φ = Prod.map₂ Lin-NNF (Lin-qelim (proj₂ (lin φ)))

module Cooper.NnfCooper where

open import Product
open import Properties
open import Properties-prop
import Normalization.Linearization as Lin
import Cooper.LinCooper as LC

import Data.Nat as Nat
import Data.Product as P

Nnf-qelim : ∀ {n} (φ : Nnf (Nat.suc n)) → Nnf n
Nnf-qelim φ with LC.Lin-qelim (Lin.lin φ)
... | ψ , Hψ = ψ , islin-isnnf Hψ
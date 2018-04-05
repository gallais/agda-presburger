module Cooper.QfreeCooper where

open import Representation
open import Properties
import Properties-prop as Pp
import Normalization.Negation as N
import Cooper.NnfCooper as NC

open import Product
open import Data.Nat

qelim : ∀ {n} (φ : Qfree (suc n)) → Qfree n
qelim φ with NC.Nnf-qelim (N.nnf φ)
... | ψ , Hψ = ψ , Pp.isnnf-isqfree Hψ
module Cooper.UnfCooper where

open import Representation
open import Properties
open import Disjunction
open import Bset
open import Cooper
import Normalization.Linearization as Lin
open import Minusinf
open import AllmostFree-prop
import Properties-prop as Pr

open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_ ; _≤?_ to _ℕ≤?_ ; _≟_ to _ℕ≟_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_ ; _≤?_ to _ℤ≤?_ ; _≟_ to _ℤ≟_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

open import Product
import Data.Vec as V
import Data.List as L
import Fin-prop as F

open import Relation.Binary.PropositionalEquality

Unf-qelim-l₁ : ∀ {n} (φ : Unf (ℕs n)) (j : Fin (jset φ)) → Lin n
Unf-qelim-l₁ φ j = Finite-disjunction′ (proj₁ φ , Pr.isunitary-islin (proj₂ φ)) (bjset φ j)

Unf-qelim-l : ∀ {n} (φ : Unf (ℕs n)) → Lin n
Unf-qelim-l φ with lcm-dvd (minusinf φ) | Unf-qelim-l₁ φ
... | δ | λφ = Fin-dij λφ (V.allFin (ℕs (δ-extract δ)))

Unf-qelim-r : ∀ {n} (φ : Unf (ℕs n)) → Lin n
Unf-qelim-r φ with lcm-dvd (minusinf φ)
... | δ = Finite-disjunction {_} {_} {0} (proj₁ (minusinf φ) , (Pr.isunitary-islin (Pr.allmost-free0-isunitary (proj₂ (minusinf φ))))) (V.map (λ u → (val (+ toℕ u) , val-islinn-i)) (V.allFin (δ-extract δ)))

Unf-qelim : ∀ {n} (φ : Unf (ℕs n)) → Lin n
Unf-qelim φ with Unf-qelim-l φ | Unf-qelim-r φ
... | φ₁ , Hφ₁ | φ₂ , Hφ₂ = φ₁ or φ₂ , or-islin Hφ₁ Hφ₂
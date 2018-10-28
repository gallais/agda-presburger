module Cooper.UnfCooper where

open import Representation
open import Properties
open import Disjunction
open import Bset
open import Cooper
open import AllmostFree-prop
open import Normalization.Linearisation
open import Minusinf
open import Properties-prop

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

open import Data.Product as Prod
import Data.Vec as Vec
import Data.List as List

open import Relation.Binary.PropositionalEquality

Unf-qelim-l₁ : ∀ {n f} (φ : Unit {ℕ.suc n} f) (j : Fin (jset φ)) → ∃ (Lin {n})
Unf-qelim-l₁ φ j = ⋁ Vec.fromList (List.map (λ e → ⟨ proj₂ e /0⟩ Unit-Lin φ) (bjset φ j))

Unf-qelim-l : ∀ {n f} → Unit {ℕ.suc n} f → ∃ (Lin {n})
Unf-qelim-l φ = ⋁[k< jset φ ] Unf-qelim-l₁ φ

Unf-qelim-r : ∀ {n f} → Unit {ℕ.suc n} f → ∃ (Lin {n})
Unf-qelim-r φ = ⋁[k< ℕ.pred (jset φ) ]⟨k/0⟩ (Free0-Lin (proj₂ (var0⟶-∞ φ)))

Unf-qelim : ∀ {n f} → Unit {ℕ.suc n} f → ∃ (Lin {n})
Unf-qelim φ = -, proj₂ (Unf-qelim-l φ) :∨ proj₂ (Unf-qelim-r φ)

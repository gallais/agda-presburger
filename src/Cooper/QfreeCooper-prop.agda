module Cooper.QfreeCooper-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Equivalence

open import Normalization.Negation
open import Normalization.Negation-prop
open import Cooper.NnfCooper
open import Cooper.NnfCooper-prop
open import Cooper.QfreeCooper

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Vec
open import Data.Product
open import Relation.Binary.SetoidReasoning

abstract

  ⟦qelim_⟧ : ∀ {n f} (φ : QFree {ℕ.suc n} f) → :∃ f ⇔ proj₁ (qelim φ)
  ⟦qelim φ ⟧ ρ = begin⟨ ↔-setoid ⟩
    ⟦ :∃ f ⟧ ρ            ≈⟨ ↔Σ (λ x → ⟦nnf φ ⟧ (x ∷ ρ)) ⟩
    ⟦ :∃ g ⟧ ρ            ≈⟨ ⟦Nnf-qelim ψ ⟧ ρ ⟩
    ⟦ proj₁ (qelim φ) ⟧ ρ ∎ where

    f     = toForm QFree φ
    g∧ψ   = nnf φ
    g     = proj₁ g∧ψ
    ψ     = proj₂ g∧ψ

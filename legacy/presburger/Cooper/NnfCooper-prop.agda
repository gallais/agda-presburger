module Cooper.NnfCooper-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Equivalence

open import Normalization.Linearisation
open import Normalization.Linearisation-prop
open import Cooper.LinCooper
open import Cooper.LinCooper-prop
open import Cooper.NnfCooper

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Vec using (_∷_)
open import Data.Product as Prod

open import Relation.Binary.SetoidReasoning

⟦Nnf-qelim_⟧ : ∀ {n f} (φ : NNF {ℕ.suc n} f) → :∃ f ⇔ proj₁ (Nnf-qelim φ)
⟦Nnf-qelim φ ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ :∃ f ⟧ ρ                ≈⟨ ↔Σ (λ x → ⟦lin φ ⟧ (x ∷ ρ)) ⟩
  ⟦ :∃ g ⟧ ρ                ≈⟨ ⟦Lin-qelim ψ ⟧ ρ ⟩
  ⟦ proj₁ (Lin-qelim ψ) ⟧ ρ ∎ where

   f     = toForm NNF φ
   g∧ψ   = lin φ
   g     = proj₁ g∧ψ
   ψ     = proj₂ g∧ψ

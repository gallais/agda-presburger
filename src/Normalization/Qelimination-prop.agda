module Normalization.Qelimination-prop where

open import Representation
open import Properties
open import Properties-prop
open import Semantics
open import Equivalence
import Normalization.Negation as Neg
import Normalization.Negation-prop as NegProp
open import Normalization.Qelimination
open import Cooper.QfreeCooper
open import Cooper.QfreeCooper-prop

-- Datatypes
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Vec

open import Function
open import Relation.Nullary as RN using (Dec; yes; no)
open import Relation.Nullary.Negation
import Relation.Nullary.Decidable as DEC
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.SetoidReasoning


Qfree-dec : ∀ {n f} (φ : QFree {n} f) ρ → Dec (⟦ f ⟧ ρ)
Qfree-dec φ ρ = let (p , q) = NegProp.⟦nnf φ ⟧ ρ in
  DEC.map′ q p (NNF? (proj₂ $ Neg.nnf φ) ρ)

⟦¬_⟧ : ∀ {n f} (φ : QFree {n} f) → (:¬ f) ⇔ proj₁ (¬ φ)
⟦¬ T        ⟧ ρ = (_$′ _) , ⊥-elim
⟦¬ F        ⟧ ρ = _ , const id
⟦¬ t₁ :< t₂ ⟧ ρ = ↔-refl
⟦¬ t₁ :> t₂ ⟧ ρ = ↔-refl
⟦¬ t₁ :≤ t₂ ⟧ ρ = ↔-refl
⟦¬ t₁ :≥ t₂ ⟧ ρ = ↔-refl
⟦¬ t₁ :≡ t₂ ⟧ ρ = ↔-refl
⟦¬ k :| t   ⟧ ρ = ↔-refl
⟦¬ :¬ φ     ⟧ ρ = decidable-stable (Qfree-dec φ ρ) , contradiction
⟦¬ φ :∧ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let f = toForm QFree φ; g = toForm QFree ψ in
  ⟦ :¬ (f :∧ g) ⟧ ρ                 ≈⟨ deMorgan-¬× (Qfree-dec φ ρ) (Qfree-dec ψ ρ) ⟩
  (RN.¬ (⟦ f ⟧ ρ) ⊎ RN.¬ (⟦ g ⟧ ρ)) ≈⟨ ⟦¬ φ ⟧ ρ ↔⊎ ⟦¬ ψ ⟧ ρ ⟩
  ⟦ proj₁ (¬ (φ :∧ ψ)) ⟧ ρ          ∎
⟦¬ φ :∨ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let f = toForm QFree φ; g = toForm QFree ψ in
  ⟦ :¬ (f :∨ g) ⟧ ρ                 ≈⟨ deMorgan-¬⊎ (Qfree-dec φ ρ) (Qfree-dec ψ ρ) ⟩
  (RN.¬ (⟦ f ⟧ ρ) × RN.¬ (⟦ g ⟧ ρ)) ≈⟨ ⟦¬ φ ⟧ ρ ↔× ⟦¬ ψ ⟧ ρ ⟩
  ⟦ proj₁ (¬ (φ :∨ ψ)) ⟧ ρ          ∎
⟦¬ φ :→ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let f = toForm QFree φ; g = toForm QFree ψ in
  ⟦ :¬ (f :→ g) ⟧ ρ            ≈⟨ deMorgan-¬→ (Qfree-dec φ ρ) ⟩
  ((⟦ f ⟧ ρ) × RN.¬ (⟦ g ⟧ ρ)) ≈⟨ ↔-refl ↔× ⟦¬ ψ ⟧ ρ ⟩
  ⟦ proj₁ (¬ (φ :→ ψ)) ⟧ ρ     ∎

⟦qfree_⟧ : ∀ {n} (f : form n) → f ⇔ proj₁ (qfree f)
⟦qfree T        ⟧ ρ = ↔-refl
⟦qfree F        ⟧ ρ = ↔-refl
⟦qfree k :| e   ⟧ ρ = ↔-refl
⟦qfree e₁ :< e₂ ⟧ ρ = ↔-refl
⟦qfree e₁ :> e₂ ⟧ ρ = ↔-refl
⟦qfree e₁ :≤ e₂ ⟧ ρ = ↔-refl
⟦qfree e₁ :≥ e₂ ⟧ ρ = ↔-refl
⟦qfree e₁ :≡ e₂ ⟧ ρ = ↔-refl
⟦qfree :¬ f     ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ :¬ f ⟧ ρ                 ≈⟨ ↔¬ ⟦qfree f ⟧ ρ ⟩
  ⟦ :¬ proj₁ (qfree f) ⟧ ρ   ≈⟨ ⟦¬ proj₂ (qfree f) ⟧ ρ ⟩
  ⟦ proj₁ (qfree (:¬ f)) ⟧ ρ ∎
⟦qfree :∃ f     ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ :∃ f ⟧ ρ                 ≈⟨ ↔Σ (λ x → ⟦qfree f ⟧ (x ∷ ρ)) ⟩
  ⟦ :∃ proj₁ (qfree f) ⟧ ρ   ≈⟨ ⟦qelim proj₂ (qfree f) ⟧ ρ ⟩
  ⟦ proj₁ (qfree (:∃ f)) ⟧ ρ ∎
⟦qfree :∀ f     ⟧ ρ = begin⟨ ↔-setoid ⟩
  ⟦ :∀ f ⟧ ρ
    ≈⟨ ↔∀ (λ x → ⟦qfree f ⟧ (x ∷ ρ)) ⟩
  (∀ x → ⟦ proj₁ (qfree f) ⟧ (x ∷ ρ))
    ≈⟨ deMorgan-∀ (λ x → Qfree-dec (proj₂ (qfree f)) (x ∷ ρ)) ⟩
  RN.¬ ∃ (λ x → ⟦ :¬ proj₁ (qfree f) ⟧ (x ∷ ρ))
    ≈⟨ ↔¬ (↔Σ (λ x → ⟦¬ proj₂ (qfree f) ⟧ (x ∷ ρ))) ⟩
  RN.¬ (⟦ :∃ proj₁ (¬ proj₂ (qfree f)) ⟧ ρ)
    ≈⟨ ↔¬ ⟦qelim proj₂ (¬ proj₂ (qfree f)) ⟧ ρ ⟩
  ⟦ :¬ proj₁ (qelim (proj₂ (¬ proj₂ (qfree f)))) ⟧ ρ
    ≈⟨ ⟦¬ proj₂ (qelim (proj₂ (¬ proj₂ (qfree f)))) ⟧ ρ ⟩
  ⟦ proj₁ (qfree (:∀ f)) ⟧ ρ ∎
⟦qfree φ :∧ ψ   ⟧ ρ = ⟦qfree φ ⟧ ρ ↔× ⟦qfree ψ ⟧ ρ
⟦qfree φ :∨ ψ   ⟧ ρ = ⟦qfree φ ⟧ ρ ↔⊎ ⟦qfree ψ ⟧ ρ
⟦qfree φ :→ ψ   ⟧ ρ = ⟦qfree φ ⟧ ρ ↔→ ⟦qfree ψ ⟧ ρ

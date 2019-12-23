module Normalization.Negation-prop where

open import Representation
open import Properties
open import Semantics
open import Equivalence
open import Normalization.Negation

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Divisibility as Ndiv
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ZProp
open import Data.Integer.Divisibility.Signed
open import Data.Fin as Fin using (Fin)

open import Data.Product as Prod
open import Data.Sum
open import Data.Empty
open import Function hiding (_↔_; _⇔_)

open import Relation.Nullary as RN using (Dec; yes; no)
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Binary.SetoidReasoning

NNF-dec : ∀ {n φ} → NNF {n} φ → ∀ ρ → Dec (⟦ φ ⟧ ρ)
NNF-dec T          ρ = yes _
NNF-dec F          ρ = no id
NNF-dec (t₁ :≤ t₂) ρ = _ ℤ.≤? _
NNF-dec (t₁ :≡ t₂) ρ = _ ℤ.≟ _
NNF-dec (t₁ :≢ t₂) ρ = ¬? (_ ℤ.≟ _)
NNF-dec (k :| t)   ρ = _ ∣? _
NNF-dec (k :|̸ t)   ρ = ¬? (_ ∣? _)
NNF-dec (p :∧ q)   ρ = (NNF-dec p ρ) ×-dec (NNF-dec q ρ)
NNF-dec (p :∨ q)   ρ = (NNF-dec p ρ) ⊎-dec (NNF-dec q ρ)

⟦¬_⟧ : ∀ {n φ} (p : NNF {n} φ) → :¬ φ ⇔ proj₁ (¬ p)
⟦¬ T        ⟧ ρ = (_$ _) , ⊥-elim
⟦¬ F        ⟧ ρ = _ , const id
⟦¬ t₁ :≤ t₂ ⟧ ρ = ZProp.≰⇒>′ , ZProp.>′⇒≰′
⟦¬ t₁ :≡ t₂ ⟧ ρ = ↔-refl
⟦¬ t₁ :≢ t₂ ⟧ ρ = decidable-stable (_ ℤ.≟ _) , _|>′_
⟦¬ k :| t   ⟧ ρ = ↔-refl
⟦¬ k :|̸ t   ⟧ ρ = decidable-stable (_ ∣? _) , _|>′_
⟦¬ φ :∧ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let p = toForm NNF φ; q = toForm NNF ψ in
  (⟦ :¬ p :∧ q ⟧ ρ)             ≈⟨ deMorgan-¬× (NNF-dec φ ρ) (NNF-dec ψ ρ) ⟩
  (RN.¬ ⟦ p ⟧ ρ ⊎ RN.¬ ⟦ q ⟧ ρ) ≈⟨ ⟦¬ φ ⟧ ρ ↔⊎ ⟦¬ ψ ⟧ ρ ⟩
  ((⟦ proj₁ (¬ φ) ⟧ ρ) ⊎ (⟦ proj₁ (¬ ψ) ⟧ ρ)) ∎
⟦¬ φ :∨ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let p = toForm NNF φ; q = toForm NNF ψ in
  (⟦ :¬ p :∨ q ⟧ ρ)             ≈⟨ deMorgan-¬⊎ (NNF-dec φ ρ) (NNF-dec ψ ρ) ⟩
  (RN.¬ ⟦ p ⟧ ρ × RN.¬ ⟦ q ⟧ ρ) ≈⟨ ⟦¬ φ ⟧ ρ ↔× ⟦¬ ψ ⟧ ρ ⟩
  ((⟦ proj₁ (¬ φ) ⟧ ρ) × (⟦ proj₁ (¬ ψ) ⟧ ρ)) ∎

⟦nnf_⟧ : ∀ {n φ} (p : QFree {n} φ) → φ ⇔ proj₁ (nnf p)
⟦nnf T        ⟧ ρ = ↔-refl
⟦nnf F        ⟧ ρ = ↔-refl
⟦nnf t₁ :< t₂ ⟧ ρ = ↔-refl
⟦nnf t₁ :> t₂ ⟧ ρ = ↔-refl
⟦nnf t₁ :≤ t₂ ⟧ ρ = ↔-refl
⟦nnf t₁ :≥ t₂ ⟧ ρ = ↔-refl
⟦nnf t₁ :≡ t₂ ⟧ ρ = ↔-refl
⟦nnf k :| t   ⟧ ρ = ↔-refl
⟦nnf :¬ φ     ⟧ ρ = begin⟨ ↔-setoid ⟩
  let p = toForm QFree φ in
  ⟦ :¬ p ⟧ ρ               ≈⟨ ↔¬ ⟦nnf φ ⟧ ρ ⟩
  RN.¬ ⟦ proj₁ (nnf φ) ⟧ ρ ≈⟨ ⟦¬ proj₂ (nnf φ) ⟧ ρ ⟩
  ⟦ proj₁ (nnf (:¬ φ)) ⟧ ρ ∎
⟦nnf φ :∧ ψ   ⟧ ρ = ⟦nnf φ ⟧ ρ ↔× ⟦nnf ψ ⟧ ρ
⟦nnf φ :∨ ψ   ⟧ ρ = ⟦nnf φ ⟧ ρ ↔⊎ ⟦nnf ψ ⟧ ρ
⟦nnf φ :→ ψ   ⟧ ρ = begin⟨ ↔-setoid ⟩
  let p = toForm QFree φ; q = toForm QFree ψ
      (p′ , φ′) = nnf φ; (q′ , ψ′) = nnf ψ in
  (⟦ p :→ q ⟧ ρ)                 ≈⟨ ⟦nnf φ ⟧ ρ ↔→ ⟦nnf ψ ⟧ ρ ⟩
  (⟦ p′ ⟧ ρ → ⟦ q′ ⟧ ρ)          ≈⟨ deMorgan-→ (NNF-dec ψ′ ρ) ⟩
  (RN.¬ (⟦ p′ ⟧ ρ) ⊎ (⟦ q′ ⟧ ρ)) ≈⟨ ⟦¬ φ′ ⟧ ρ ↔⊎ ↔-refl ⟩
  (⟦ proj₁ (nnf (φ :→ ψ)) ⟧ ρ)   ∎

module Normalization.Qelimination where

open import Representation
open import Properties
open import Properties-prop
open import Cooper.QfreeCooper

open import Data.Product

-- Datatypes
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

infix 3 ¬_
¬_ : ∀ {n φ} → QFree {n} φ → ∃ (QFree {n})
¬ T          = -, F
¬ F          = -, T
¬ (t₁ :< t₂) = -, :¬ (t₁ :< t₂)
¬ (t₁ :> t₂) = -, :¬ (t₁ :> t₂)
¬ (t₁ :≤ t₂) = -, :¬ (t₁ :≤ t₂)
¬ (t₁ :≥ t₂) = -, :¬ (t₁ :≥ t₂)
¬ (t₁ :≡ t₂) = -, :¬ (t₁ :≡ t₂)
¬ (k :| t)   = -, :¬ (k :| t)
¬ (:¬ p)     = -, p
¬ (p :∧ q)   = -, proj₂ (¬ p) :∨ proj₂ (¬ q)
¬ (p :∨ q)   = -, proj₂ (¬ p) :∧ proj₂ (¬ q)
¬ (p :→ q)   = -, p :∧ proj₂ (¬ q)

qfree : ∀ {n} → form n → ∃ (QFree {n})
qfree T          = -, T
qfree F          = -, F
qfree (k :| e)   = -, k :| e
qfree (e₁ :< e₂) = -, e₁ :< e₂
qfree (e₁ :> e₂) = -, e₁ :> e₂
qfree (e₁ :≤ e₂) = -, e₁ :≤ e₂
qfree (e₁ :≥ e₂) = -, e₁ :≥ e₂
qfree (e₁ :≡ e₂) = -, e₁ :≡ e₂
qfree (:¬ φ)     = ¬ proj₂ (qfree φ)
qfree (:∃ φ)     = qelim (proj₂ (qfree φ))
qfree (:∀ φ)     = ¬ proj₂ (qelim (proj₂ (¬ proj₂ (qfree φ))))
qfree (φ :∧ ψ)   = -, proj₂ (qfree φ) :∧ proj₂ (qfree ψ)
qfree (φ :∨ ψ)   = -, proj₂ (qfree φ) :∨ proj₂ (qfree ψ)
qfree (φ :→ ψ)   = -, proj₂ (qfree φ) :→ proj₂ (qfree ψ)

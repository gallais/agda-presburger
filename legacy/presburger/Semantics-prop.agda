module Semantics-prop where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

open import Relation.Binary.PropositionalEquality

open import Data.Vec
open import Data.Vec.Relation.Pointwise.Inductive using (Pointwise; Pointwise-≡⇒≡)
open import Function

open import Representation
open import Properties
open import Semantics

⟦_⟧-ext : ∀ {n} (f : form n) {ρ₁ ρ₂} → Pointwise _≡_ ρ₁ ρ₂ → ⟦ f ⟧ ρ₁ → ⟦ f ⟧ ρ₂
⟦ f ⟧-ext ρ rewrite Pointwise-≡⇒≡ ρ = id

lin-ext₁ : ∀ {n n₀ t} (e : Lin-E {ℕ.suc n} (ℕ.suc n₀) t) x₁ x₂ ρ →
           ⟦ t ⟧e (x₁ ∷ ρ) ≡ ⟦ t ⟧e (x₂ ∷ ρ)
lin-ext₁ (val k)                       x₁ x₂ ρ = refl
lin-ext₁ (k *var Fin.suc p [ prf ]+ e) x₁ x₂ ρ =
  cong (ℤ._+_ (toℤ k ℤ.* lookup p ρ)) (lin-ext₁ e x₁ x₂ ρ)

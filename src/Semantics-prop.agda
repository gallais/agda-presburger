module Semantics-prop where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)

open import Relation.Binary.PropositionalEquality

open import Data.Vec
import Data.Vec.Relation.Pointwise.Inductive as VecEq
open import Function

open import Representation
open import Properties
open import Semantics

⟦_⟧-ext : ∀ {n} (f : form n) {ρ₁ ρ₂} → VecEq.Pointwise _≡_ ρ₁ ρ₂ → ⟦ f ⟧ ρ₁ → ⟦ f ⟧ ρ₂
⟦ f ⟧-ext ρ rewrite VecEq.Pointwise-≡⇒≡ ρ = id

⟦_⟧-ext₁ : ∀ {n} (f : form (ℕ.suc n)) {x y ρ} → x ≡ y → ⟦ f ⟧ (x ∷ ρ) → ⟦ f ⟧ (y ∷ ρ)
⟦ f ⟧-ext₁ x = ⟦ f ⟧-ext (x VecEq.∷ VecEq.refl refl)

lin-ext₁ : ∀ {n n₀ t} (e : Lin-E {ℕ.suc n} (ℕ.suc n₀) t) x₁ x₂ ρ →
           ⟦ t ⟧e (x₁ ∷ ρ) ≡ ⟦ t ⟧e (x₂ ∷ ρ)
lin-ext₁ (val k)                       x₁ x₂ ρ = refl
lin-ext₁ (k *var Fin.suc p [ prf ]+ e) x₁ x₂ ρ =
  cong (ℤ._+_ (toℤ k ℤ.* lookup ρ p)) (lin-ext₁ e x₁ x₂ ρ)

module problem.semantics where

{- Semantics à la Tarski for expressions and formulas within
   an environment. A legal transformation of a formula is one
   that is meaning-preserving in any environment. -}

open import Data.Integer as ℤ
open import Data.Vec as V

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Data.Integer.Divisibility

open import problem.definition

⟦_⟧e_ : ∀ {n} (e : exp n) (ρ : Vec ℤ n) → ℤ
⟦ val k ⟧e ρ = k
⟦ var p ⟧e ρ = lookup p ρ
⟦ :- e ⟧e ρ = - ⟦ e ⟧e ρ
⟦ e₁ :+ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ ℤ.+ ⟦ e₂ ⟧e ρ
⟦ e₁ :- e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ ℤ.- ⟦ e₂ ⟧e ρ
⟦ k :* e ⟧e ρ = k ℤ.* ⟦ e ⟧e ρ

⟦_⟧_ : ∀ {n} (φ : form n) (ρ : Vec ℤ n) → Set
⟦ :⊤ ⟧ ρ = ⊤
⟦ :⊥ ⟧ ρ = ⊥
⟦ k :| e ⟧ ρ = k ∣ ⟦ e ⟧e ρ
⟦ e₁ :< e₂ ⟧ ρ = ℤ.suc (⟦ e₁ ⟧e ρ) ℤ.≤ ⟦ e₂ ⟧e ρ
⟦ e₁ :> e₂ ⟧ ρ = ℤ.suc (⟦ e₂ ⟧e ρ) ℤ.≤ ⟦ e₁ ⟧e ρ
⟦ e₁ :≤ e₂ ⟧ ρ = ⟦ e₁ ⟧e ρ ℤ.≤ ⟦ e₂ ⟧e ρ
⟦ e₁ :≥ e₂ ⟧ ρ = ⟦ e₂ ⟧e ρ ℤ.≤ ⟦ e₁ ⟧e ρ
⟦ e₁ :≡ e₂ ⟧ ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ 
⟦ :¬ φ ⟧ ρ = ⟦ φ ⟧ ρ → ⊥
⟦ :∃ φ ⟧ ρ = ∃ (λ k → ⟦ φ ⟧ (k ∷ ρ))
⟦ :∀ φ ⟧ ρ = ∀ k → ⟦ φ ⟧ (k ∷ ρ)
⟦ φ₁ :∧ φ₂ ⟧ ρ = ⟦ φ₁ ⟧ ρ × ⟦ φ₂ ⟧ ρ
⟦ φ₁ :∨ φ₂ ⟧ ρ = ⟦ φ₁ ⟧ ρ ⊎ ⟦ φ₂ ⟧ ρ
⟦ φ₁ :→ φ₂ ⟧ ρ = ⟦ φ₁ ⟧ ρ → ⟦ φ₂ ⟧ ρ

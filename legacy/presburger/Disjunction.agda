module Disjunction where

open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec
open import Data.Product as Prod
open import Function

open import Relation.Binary.PropositionalEquality

open import Properties
open import Properties-prop
open import Normalization.Linearisation
open import Normalization.LCMReduction
open import Normalization.Unitarization

infix 3 ⋁_

⋁_ : ∀ {m n} → Vec (∃ (Lin {n})) m → ∃ (Lin {n})
⋁_ = Vec.foldr _ (λ φ ψ → -, proj₂ φ :∨ proj₂ ψ) (-, F)


lin-E⁻ : ∀ {n p e} → Lin-E {ℕ.suc n} (ℕ.suc p) e → ∃ (Lin-E {n} p)
lin-E⁻ (val k)                       = -, val k
lin-E⁻ (k *var Fin.zero  [ () ]+ e)
lin-E⁻ (k *var Fin.suc p [ ℕ.s≤s prf ]+ e) = -, k *var p [ prf ]+ proj₂ (lin-E⁻ e)

unit-E⁻ : ∀ {n p e} → Lin-E {ℕ.suc n} (ℕ.suc p) e → ∃ (Unit-E {n})
unit-E⁻ e = unit-E (proj₂ (div-E (proj₂ (lin-E⁻ e))))

⟨_/0⟩-E_ : ∀ {n p p' e f} → Lin-E {ℕ.suc n} (ℕ.suc p) e → Lin-E {ℕ.suc n} p' f →
           ∃ (Lin-E {ℕ.suc n} 1)
⟨ f /0⟩-E val k                         = -, val k
⟨ f /0⟩-E (k *var Fin.zero  [ prf ]+ e) = Lin-E^wk (ℕ.s≤s ℕ.z≤n) (proj₂ (k ≠0*E f)) +E e
⟨ f /0⟩-E (k *var Fin.suc p [ prf ]+ e) = -, k *var Fin.suc p [ ℕ.s≤s ℕ.z≤n ]+ e

⟨_/0⟩-E⁻_ : ∀ {n p p' e f} → Lin-E {ℕ.suc n} (ℕ.suc p) e → Lin-E {ℕ.suc n} p' f →
            ∃ (Lin-E {n} 0)
⟨ f /0⟩-E⁻ e = lin-E⁻ (proj₂ (⟨ f /0⟩-E e))

⟨_/0⟩_ : ∀ {n p f φ} → Lin-E {ℕ.suc n} (ℕ.suc p) f → Lin {ℕ.suc n} φ → ∃ (Lin {n})
⟨ f /0⟩ T        = -, T
⟨ f /0⟩ F        = -, F
⟨ f /0⟩ (e :≤0)  = -, proj₂ (⟨ f /0⟩-E⁻ e) :≤0
⟨ f /0⟩ (e :≡0)  = -, proj₂ (⟨ f /0⟩-E⁻ e) :≡0
⟨ f /0⟩ (e :≢0)  = -, proj₂ (⟨ f /0⟩-E⁻ e) :≢0
⟨ f /0⟩ (k :| e) = -, k :| proj₂ (⟨ f /0⟩-E⁻ e)
⟨ f /0⟩ (k :|̸ e) = -, k :|̸ proj₂ (⟨ f /0⟩-E⁻ e)
⟨ f /0⟩ (φ :∧ ψ) = -, proj₂ (⟨ f /0⟩ φ) :∧ proj₂ (⟨ f /0⟩ ψ)
⟨ f /0⟩ (φ :∨ ψ) = -, proj₂ (⟨ f /0⟩ φ) :∨ proj₂ (⟨ f /0⟩ ψ)

⋁[k<_]_ : ∀ {n φ} → ℕ → Lin {ℕ.suc n} φ → ∃ (Lin {n})
⋁[k< σ ] φ = ⋁_
           $ Vec.map (λ k → ⟨ (val {n₀ = 1} (ℤ.+ Fin.toℕ k)) /0⟩ φ)
           $ Vec.allFin σ

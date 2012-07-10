module problem.semantics-prop where

open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F renaming (suc to Fs)

open import Relation.Binary.PropositionalEquality

open import Data.Product
open import Data.Vec

open import problem.definition
open import problem.semantics
open import problem.properties

{- When an expression does not use [var 0], its interpretation is
   the same in environments that agrees everywhere except on their
   first component. -}

abstract

  context-simpl : ∀ {n p} (e : ELin (ℕ.suc n) (ℕ.suc p)) x₁ x₂ ρ →
                  ⟦ proj₁ e ⟧e (x₁ ∷ ρ) ≡ ⟦ proj₁ e ⟧e (x₂ ∷ ρ)
  context-simpl (._ , val-elin {k = k}) x₁ x₂ ρ = refl
  context-simpl (._ , var-elin {k = k} {p = zero} {r = r} k≠0 () Hr) x₁ x₂ ρ
  context-simpl (._ , var-elin {k = k} {p = Fs n} {r = r} k≠0 n₀≤p Hr) x₁ x₂ ρ =
   cong (λ r → k ℤ.* lookup n ρ ℤ.+ r) (context-simpl (r , Hr) x₁ x₂ ρ)
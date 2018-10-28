module Presburger where

open import Representation
open import Semantics
open import Normalization.Qelimination
open import Normalization.Qelimination-prop
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable

dec : ∀ {n} (f : form n) ρ → Dec (⟦ f ⟧ ρ)
dec f ρ = map′ (proj₂ correct) (proj₁ correct) (Qfree-dec (proj₂ (qfree f)) ρ)
  where correct = ⟦qfree f ⟧ ρ

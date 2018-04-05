module Lcm where

open import Data.Nat
open import Data.Integer
open import Product
open import Data.Empty

open import Properties
open import Integer.LCM

open import Relation.Binary.PropositionalEquality

lcm₂ : ∀ (p q : ℤ) → ∃ (LCM p q)
lcm₂ p q = {!!}

postulate
  lcm₂-neq : ∀ (m n : Notnull) {d} → LCM (proj₁ m) (proj₁ n) d → (+ d ≡ + 0 → ⊥)
-- This module is mainly based on Data.Nat.LCM

module Integer.LCM where

open import Data.Nat
open import Data.Integer
open import Data.Integer.Divisibility
open import Data.Product


-----
-- Least common multiple
-----

module LCM where

  -- specification of the lcm of two integers

  record LCM (i j : ℤ) (d : ℕ) : Set where
    constructor lcm
    field
      -- it is a common multiple
      commonMultiple : (i ∣ (+ d)) × (j ∣ (+ d))

      -- it divides all the other common multiples
      least : ∀ {m} → (i ∣ m) × (j ∣ m) → (+ d) ∣ m

  open LCM public

open LCM public using (LCM)
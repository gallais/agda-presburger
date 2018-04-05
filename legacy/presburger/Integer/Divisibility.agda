module Integer.Divisibility where

open import Data.Integer
open import Data.Integer.Divisibility
open import Data.Nat.Divisibility using () renaming (_∣?_ to _ℕ∣?_)

open import Relation.Binary

-- Decidability

abstract

  _∣?_ : Decidable _∣_
  k ∣? p = _ℕ∣?_ (∣ k ∣) (∣ p ∣)
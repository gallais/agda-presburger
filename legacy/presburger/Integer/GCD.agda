-- This module is mainly based on Data.Nat.GCD

module Integer.GCD where

open import Data.Nat renaming (_+_ to _ℕ+_ ; suc to S)
open import Data.Integer renaming (_+_ to _ℤ+_ ; _*_ to _ℤ*_)
open import Data.Integer.Divisibility
open import Data.Nat.Divisibility as Div renaming (_∣_ to _dvd_)
open import Data.Product

open import Relation.Binary
private module P = Poset Div.poset
open import Function

open import Relation.Binary.PropositionalEquality using (_≡_  ; cong ; sym ; cong₂ ; subst ; subst₂)
 renaming (refl to ≡-refl)

open import Data.Integer.Properties as IntProp renaming (abs-cong to abs-cong′)
open import Data.Integer.Divisibility as Div2

open import Aux

module GCD where

  -- specification of the greatest common divisor of two integers

  record GCD (i j : ℤ) (gcd : ℕ) : Set where
    constructor is
    field
      -- it is a common divisor
      commonDivisor : ((+ gcd) ∣ i) × ((+ gcd) ∣ j)

      -- it is the greatest one
      greatest : ∀ {m} → (m ∣ i) × (m ∣ j) → m ∣ (+ gcd)

  open GCD public

  -- uniqueness
  unique : ∀ {d₁ d₂ i j} → GCD i j d₁ → GCD i j d₂ → d₁ ≡ d₂
  unique {d₁} {d₂} (is y y') (is y0 y1) = P.antisym (y1 {+ d₁} y) (y' {+ d₂} y0)

  -- symmetry
  sym' : ∀ {d i j} → GCD i j d → GCD j i d
  sym' {d} {i} {j} H = is (swap $ commonDivisor H) (λ {m} x → greatest H {m} (swap x))

  -- reflexivity
  refl : ∀ {n} → GCD n n ∣ n ∣
  refl = is (P.refl , P.refl) proj₁

open GCD public using (GCD ; is)
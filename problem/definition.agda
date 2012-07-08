module problem.definition where

{- Definition of the class of problems we want to solve. -}

open import Data.Nat as ℕ
open import Data.Fin as F
open import Data.Integer as ℤ

-- expression with n variables

data exp (n : ℕ) : Set where
 val : ∀ (k : ℤ) → exp n
 var : ∀ (p : Fin n) → exp n
 :-_ : ∀ (e : exp n) → exp n
 _:+_ _:-_ : ∀ (e₁ e₂ : exp n) → exp n
 _:*_ : ∀ (k : ℤ) (e : exp n) → exp n

-- formulas with n variables

data form (n : ℕ) : Set where
 :⊤ :⊥ : form n
 _:|_ : ∀ (k : ℤ) (e : exp n) → form n
 _:<_ _:>_ _:≤_ _:≥_ _:≡_ : ∀ (e₁ e₂ : exp n) → form n
 :¬_ : ∀ (φ : form n) → form n
 :∃_ :∀_ : ∀ (φ : form (ℕ.suc n)) → form n
 _:∧_ _:∨_ _:→_ : ∀ (φ₁ φ₂ : form n) → form n
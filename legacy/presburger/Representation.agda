module Representation where

open import Data.Nat as ℕ
open import Data.Fin as F
open import Data.Integer as ℤ

-----
-- Data structures
-----

-- expressions

infix 22 :-_
infix 23 _:+_ _:-_
infix 24 _:*_

data exp (n : ℕ) : Set where
 val       : (k : ℤ) → exp n
 var       : (p : Fin n) → exp n
 :-_       : (e : exp n) → exp n
 _:+_ _:-_ : (e₁ e₂ : exp n) → exp n
 _:*_      : (k : ℤ) (e : exp n) → exp n

-- formulas

infix 15 :∃_ :∀_
infix 16 _:→_
infix 17 :¬_
infixr 18 _:∨_
infixr 19 _:∧_
infix 20 _:|_ _:<_ _:>_ _:≤_ _:≥_ _:≡_

data form (n : ℕ) : Set where
 T F                      : form n
 _:|_                     : (k : ℤ) (e : exp n) → form n
 _:<_ _:>_ _:≤_ _:≥_ _:≡_ : (e₁ e₂ : exp n) → form n
 :¬_                      : (φ : form n) → form n
 :∃_ :∀_                  : (φ : form (ℕ.suc n)) → form n
 _:∧_ _:∨_ _:→_           : (φ₁ φ₂ : form n) → form n

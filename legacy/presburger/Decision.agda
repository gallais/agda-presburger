module Decision where

open import Representation
open import Properties
open import Semantics
open import Product

open import Normalization.Qelimination
open import Normalization.Qelimination-prop

-- About ≡ and Dec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

import Data.Product as P

-- Datatypes
open import Data.Nat as Nat renaming (suc to ℕs ; pred to ℕp ; _+_ to _ℕ+_ ; _*_ to _ℕ*_ ; _≤_ to _ℕ≤_ ; _⊔_ to _ℕ⊔_ ; _⊓_ to _ℕ⊓_)
open import Data.Integer as Int renaming (suc to ℤs ; pred to ℤp ; _+_ to _ℤ+_ ; _*_ to _ℤ*_ ; _-_ to _ℤ-_ ; _≤_ to _ℤ≤_ ; _⊔_ to _ℤ⊔_ ; _⊓_ to _ℤ⊓_)
open import Data.Fin renaming (suc to Fs ; _≤_ to _F≤_)

Presburger-dec : ∀ {n} (φ : form n) ρ → Dec ([| φ |] ρ)
Presburger-dec φ ρ with qfree-sem φ ρ | Qfree-dec (qfree φ) ρ
... | P._,_ P Q | yes H = yes (Q H)
... | P._,_ P Q | no ¬H = no (λ x → ¬H (P x))
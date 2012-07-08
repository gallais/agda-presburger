module problem.equivalence where

{- Definition of problem equivalence as equivalence
   after evaluation in any environment. -}

open import Data.Nat as ℕ
open import Data.Vec as V

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import problem.definition
open import problem.semantics

------------------------------------------------------------------------
-- What it means for two formulas to be equivalent.

infix 3 _←_ _↔_ _⇐_ _⇔_ _⇒_

_←_ : Set → Set → Set
P ← Q = Q → P

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (P ← Q)

_⇒_ : ∀ {n}(φ₁ φ₂ : form n) → Set
φ₁ ⇒ φ₂ = ∀ ρ → ⟦ φ₁ ⟧ ρ → ⟦ φ₂ ⟧ ρ

_⇔_ : ∀ {n}(φ₁ φ₂ : form n) → Set
φ₁ ⇔ φ₂ = ∀ ρ → ⟦ φ₁ ⟧ ρ ↔ ⟦ φ₂ ⟧ ρ

_⇐_ : ∀ {n}(φ₁ φ₂ : form n) → Set
_⇐_ = flip _⇒_

infix 1 [_]⤇[_]_■[_]⤆[_]_■

[_]⤇[_]_■[_]⤆[_]_■ : ∀ (A B : Set) (pr : A → B) (C D : Set) (pr : D → C) →
                        (A → B) × (D → C)
[ A ]⤇[ B ] pAB ■[ C ]⤆[ D ] pDC ■ = pAB , pDC
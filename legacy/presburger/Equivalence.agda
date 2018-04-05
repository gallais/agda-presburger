------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------
module Equivalence where

open import Data.Nat
open import Data.Vec
open import Function
open import Product
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; isEquivalence ; refl)

open import Representation
open import Semantics

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
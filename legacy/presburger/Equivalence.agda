------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------
module Equivalence where

open import Data.Nat
open import Data.Vec
open import Function
open import Data.Product as Prod
open import Data.Sum as Sum
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; isEquivalence ; refl)

open import Representation
open import Semantics

------------------------------------------------------------------------
-- What it means for two formulas to be equivalent.

infix 2 _←_ _↔_ _⇐_ _⇔_ _⇒_

_←_ : Set → Set → Set
P ← Q = Q → P

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (P ← Q)

↔-refl : ∀ {P} → P ↔ P
↔-refl = id , id

↔-sym : ∀ {P Q} → P ↔ Q → Q ↔ P
↔-sym = Prod.swap

deMorgan-¬× : ∀ {P Q} → Dec P → Dec Q → ¬ (P × Q) ↔ (¬ P ⊎ ¬ Q)
proj₁ (deMorgan-¬× P? Q?) ¬p×q with P? | Q?
... | yes p | yes q = inj₁ (λ x → ¬p×q (x , q))
... | yes p | no ¬q = inj₂ (λ x → ¬p×q (p , x))
... | no ¬p | yes q = inj₁ (λ x → ¬p×q (x , q))
... | no ¬p | no ¬q = inj₁ ¬p
proj₂ (deMorgan-¬× P? Q?) ¬p⊎¬q (p , q) = [ _$′ p , _$′ q ]′ ¬p⊎¬q

deMorgan-¬⊎ : ∀ {P Q} → Dec P → Dec Q → ¬ (P ⊎ Q) ↔ (¬ P × ¬ Q)
proj₁ (deMorgan-¬⊎ P? Q?) ¬p⊎q with P? | Q?
... | yes p | yes q = (λ x → ¬p⊎q (inj₁ x)) , (λ x → ¬p⊎q (inj₁ p))
... | yes p | no ¬q = (λ x → ¬p⊎q (inj₁ x)) , ¬q
... | no ¬p | yes q = ¬p , (λ x → ¬p⊎q (inj₂ x))
... | no ¬p | no ¬q = ¬p , ¬q
proj₂ (deMorgan-¬⊎ P? Q?) (¬p , ¬q) p⊎q = [ ¬p , ¬q ]′ p⊎q

deMorgan-→ : ∀ {P Q} → Dec Q → (P → Q) ↔ (¬ P ⊎ Q)
proj₁ (deMorgan-→ Q?) f with Q?
... | yes q = inj₂ q
... | no ¬q = inj₁ (contraposition f ¬q)
proj₂ (deMorgan-→ Q?) = [ flip contradiction , const ]′

_⇒_ : ∀ {n}(φ₁ φ₂ : form n) → Set
φ₁ ⇒ φ₂ = ∀ ρ → ⟦ φ₁ ⟧ ρ → ⟦ φ₂ ⟧ ρ

_⇔_ : ∀ {n}(φ₁ φ₂ : form n) → Set
φ₁ ⇔ φ₂ = ∀ ρ → ⟦ φ₁ ⟧ ρ ↔ ⟦ φ₂ ⟧ ρ

_⇔e_ : ∀ {n} (e f : exp n) → Set
e ⇔e f = ∀ ρ → ⟦ e ⟧e ρ ≡ ⟦ f ⟧e ρ

_⇐_ : ∀ {n}(φ₁ φ₂ : form n) → Set
_⇐_ = flip _⇒_

_↔⊎_ : ∀ {P Q R S} → P ↔ Q → R ↔ S → (P ⊎ R) ↔ (Q ⊎ S)
proj₁ (f ↔⊎ g) = Sum.map (proj₁ f) (proj₁ g)
proj₂ (f ↔⊎ g) = Sum.map (proj₂ f) (proj₂ g)

_↔×_ : ∀ {P Q R S} → P ↔ Q → R ↔ S → (P × R) ↔ (Q × S)
proj₁ (f ↔× g) = Prod.map (proj₁ f) (proj₁ g)
proj₂ (f ↔× g) = Prod.map (proj₂ f) (proj₂ g)

↔Σ_ : ∀ {A P Q} → (∀ a → P a ↔ Q a) → (Σ A P) ↔ (Σ A Q)
proj₁ (↔Σ f) = Prod.map₂ (proj₁ (f _))
proj₂ (↔Σ f) = Prod.map₂ (proj₂ (f _))

↔¬_ : ∀ {P Q} → P ↔ Q → ¬ P ↔ ¬ Q
proj₁ (↔¬ f) = contraposition (proj₂ f)
proj₂ (↔¬ f) = contraposition (proj₁ f)

_↔→_ : ∀ {P Q R S} → P ↔ Q → R ↔ S → (P → R) ↔ (Q → S)
proj₁ (f ↔→ g) = λ p→r q → proj₁ g (p→r (proj₂ f q))
proj₂ (f ↔→ g) = λ q→s p → proj₂ g (q→s (proj₁ f p))

↔-setoid : Setoid _ _
Setoid.Carrier       ↔-setoid = Set
Setoid._≈_           ↔-setoid = _↔_
Setoid.isEquivalence ↔-setoid = record
  { refl  = ↔-refl
  ; sym   = ↔-sym
  ; trans = uncurry λ f₁ f₂ → uncurry λ g₁ g₂ → g₁ ∘′ f₁ , f₂ ∘′ g₂
  }

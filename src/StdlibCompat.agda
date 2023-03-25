module StdlibCompat where

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.MultiSetoid as ≋-Reasoning

module _ {c ℓ} {S : Setoid c ℓ} where

  open Setoid S renaming (_≈_ to _≈_)

  _↔⟨_⟩_ : ∀ x {y z} → x ≈ y → ≋-Reasoning.IsRelatedTo S y z → ≋-Reasoning.IsRelatedTo S x z
  x ↔⟨ x≡y ⟩ y≡z = ≋-Reasoning.step-≈ x y≡z x≡y
  infixr 2 _↔⟨_⟩_

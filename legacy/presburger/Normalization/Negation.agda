module Normalization.Negation where

open import Representation
open import Properties

open import Product
open import Data.Nat
open import Data.Integer
open import Data.Fin

{- Negation normal form is a normal form for formulas where:
   - the formulas are quantifier free
   - negations are pushed inside using De Morgan's laws
   - all the inequalities are expressed in terms of _≤_

   Using De Morgan's laws is not a problem given that we will
   be able to decide the truth value of a formula in nnf and
   therefore justify this simplification.
-}

{- [neg φ] transforms a formula in negation normal form in its
   negation.
   [nnf φ] turns a quantifier free formula into a formula in
   negation normal form. -}

neg : ∀ {n} (φ : Nnf n) → Nnf n
neg (.T , T-isnnf) = F , F-isnnf
neg (.F , F-isnnf) = T , T-isnnf
neg (.(t₁ :≤ t₂) , :≤-isnnf {t₁} {t₂}) = (:1 :+ t₁) :≤ t₂ , :≤-isnnf
neg (.(t₁ :≡ t₂) , :≡-isnnf {t₁} {t₂}) = :¬ (t₁ :≡ t₂) , :≢-isnnf
neg (.(:¬ (t₁ :≡ t₂)) , :≢-isnnf {t₁} {t₂}) = t₁ :≡ t₂ , :≡-isnnf
neg (.(k :| t₁) , :|-isnnf {k} {t₁}) = :¬ (k :| t₁) , :|̸-isnnf
neg (.(:¬ (k :| t₁)) , :|̸-isnnf {k} {t₁}) = k :| t₁ , :|-isnnf
neg (.(φ₁ :∧ φ₂) , :∧-isnnf {φ₁} {φ₂} pr₁ pr₂) with neg (φ₁ , pr₁) | neg (φ₂ , pr₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∨ ψ₂ , :∨-isnnf Hψ₁ Hψ₂
neg (.(φ₁ :∨ φ₂) , :∨-isnnf {φ₁} {φ₂} pr₁ pr₂) with neg (φ₁ , pr₁) | neg (φ₂ , pr₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∧ ψ₂ , :∧-isnnf Hψ₁ Hψ₂

nnf : ∀ {n} (φ : Qfree n) → Nnf n
nnf (.T , T-isqfree) = T , T-isnnf
nnf (.F , F-isqfree) = F , F-isnnf
nnf (.(t₁ :< t₂) , :<-isqfree {t₁} {t₂}) = (:1 :+ t₁) :≤ t₂ , :≤-isnnf
nnf (.(t₁ :> t₂) , :>-isqfree {t₁} {t₂}) = (:1 :+ t₂) :≤ t₁ , :≤-isnnf
nnf (.(t₁ :≤ t₂) , :≤-isqfree {t₁} {t₂}) = t₁ :≤ t₂ , :≤-isnnf
nnf (.(t₁ :≥ t₂) , :≥-isqfree {t₁} {t₂}) = t₂ :≤ t₁ , :≤-isnnf
nnf (.(t₁ :≡ t₂) , :≡-isqfree {t₁} {t₂}) = t₁ :≡ t₂ , :≡-isnnf
nnf (.(k :| t₁) , :|-isqfree {k} {t₁}) = k :| t₁ , :|-isnnf
nnf (.(:¬ φ) , :¬-isqfree {φ} pr) = neg (nnf (φ , pr))
nnf (.(φ₁ :∧ φ₂) , :∧-isqfree {φ₁} {φ₂} pr₁ pr₂) with nnf (φ₁ , pr₁) | nnf (φ₂ , pr₂)
... | ψ₁ , Hψ₁ | ψ₂ , HΨ₂ = ψ₁ :∧ ψ₂ , :∧-isnnf Hψ₁ HΨ₂
nnf (.(φ₁ :∨ φ₂) , :∨-isqfree {φ₁} {φ₂} pr₁ pr₂) with nnf (φ₁ , pr₁) | nnf (φ₂ , pr₂)
... | ψ₁ , Hψ₁ | ψ₂ , HΨ₂ = ψ₁ :∨ ψ₂ , :∨-isnnf Hψ₁ HΨ₂
nnf (.(φ₁ :→ φ₂) , :→-isqfree {φ₁} {φ₂} pr₁ pr₂) with neg (nnf (φ₁ , pr₁)) | nnf (φ₂ , pr₂)
... | ψ₁ , Hψ₁ | ψ₂ , HΨ₂ = ψ₁ :∨ ψ₂ , :∨-isnnf Hψ₁ HΨ₂
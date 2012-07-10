module normalize.negation where

open import problem.definition
open import problem.properties

open import Data.Product
open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Fin as F

{- Negation normal form is a normal form for formulas where:
   - the formulas are quantifier free
   - negations are pushed inwards using De Morgan's laws
   - all the inequalities are expressed in terms of _≤_
   Using De Morgan's laws is not a problem given that we will
   be able to decide the truth value of a formula in nnf and
   therefore justify this simplification.
  
   [nnf-neg φ] transforms a formula in negation normal form
   in its negation. [qfree-nnf φ] turns a quantifier free
   formula into a formula in negation normal form. -}

nnf-neg : ∀ {n} (φ : Nnf n) → Nnf n
nnf-neg (.(t₁ :≤ t₂) , :≤-nnf {t₁} {t₂}) = (t₂ :+ :1) :≤ t₁ , :≤-nnf
nnf-neg (.(t₁ :≡ t₂) , :≡-nnf {t₁} {t₂}) = :¬ (t₁ :≡ t₂) , :≢-nnf
nnf-neg (.(:¬ (t₁ :≡ t₂)) , :≢-nnf {t₁} {t₂}) = t₁ :≡ t₂ , :≡-nnf
nnf-neg (.(k :| t) , :|-nnf {k} {t}) = :¬ (k :| t) , :|̸-nnf
nnf-neg (.(:¬ (k :| t)) , :|̸-nnf {k} {t}) = k :| t , :|-nnf
nnf-neg (.(φ₁ :∧ φ₂) , :∧-nnf {φ₁} {φ₂} Hφ₁ Hφ₂) with nnf-neg (_ , Hφ₁) | nnf-neg (_ , Hφ₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∨ ψ₂ , :∨-nnf Hψ₁ Hψ₂
nnf-neg (.(φ₁ :∨ φ₂) , :∨-nnf {φ₁} {φ₂} Hφ₁ Hφ₂) with nnf-neg (_ , Hφ₁) | nnf-neg (_ , Hφ₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∧ ψ₂ , :∧-nnf Hψ₁ Hψ₂

qfree-nnf : ∀ {n} (φ : Qfree n) → Nnf n
qfree-nnf (.(t₁ :< t₂) , :<-qf {t₁} {t₂}) = (t₁ :+ :1) :≤ t₂ , :≤-nnf
qfree-nnf (.(t₁ :> t₂) , :>-qf {t₁} {t₂}) = (t₂ :+ :1) :≤ t₁ , :≤-nnf
qfree-nnf (.(t₁ :≤ t₂) , :≤-qf {t₁} {t₂}) = t₁ :≤ t₂ , :≤-nnf
qfree-nnf (.(t₁ :≥ t₂) , :≥-qf {t₁} {t₂}) = t₂ :≤ t₁ , :≤-nnf
qfree-nnf (.(t₁ :≡ t₂) , :≡-qf {t₁} {t₂}) = t₁ :≡ t₂ , :≡-nnf
qfree-nnf (.(k :| t₁) , :|-qf {k} {t₁}) = k :| t₁ , :|-nnf
qfree-nnf (.(:¬ φ) , :¬-qf {φ} Hφ) = nnf-neg (qfree-nnf (φ , Hφ))
qfree-nnf (.(φ₁ :∧ φ₂) , :∧-qf {φ₁} {φ₂} Hφ₁ Hφ₂) with qfree-nnf (_ , Hφ₁) | qfree-nnf (_ , Hφ₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∧ ψ₂ , :∧-nnf Hψ₁ Hψ₂
qfree-nnf (.(φ₁ :∨ φ₂) , :∨-qf {φ₁} {φ₂} Hφ₁ Hφ₂) with qfree-nnf (_ , Hφ₁) | qfree-nnf (_ , Hφ₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∨ ψ₂ , :∨-nnf Hψ₁ Hψ₂
qfree-nnf (.(φ₁ :→ φ₂) , :→-qf {φ₁} {φ₂} Hφ₁ Hφ₂)
  with nnf-neg (qfree-nnf (_ , Hφ₁)) | qfree-nnf (_ , Hφ₂)
... | ψ₁ , Hψ₁ | ψ₂ , Hψ₂ = ψ₁ :∨ ψ₂ , :∨-nnf Hψ₁ Hψ₂
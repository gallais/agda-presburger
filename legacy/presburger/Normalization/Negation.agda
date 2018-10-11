module Normalization.Negation where

open import Representation
open import Properties

open import Data.Product
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


infix 3 ¬_

¬_ : ∀ {n φ} → NNF {n} φ → ∃ (NNF {n})
¬ T          = -, F
¬ F          = -, T
¬ (t₁ :≤ t₂) = -, ((:1 :+ t₂) :≤ t₁)
¬ (t₁ :≡ t₂) = -, (t₁ :≢ t₂)
¬ (t₁ :≢ t₂) = -, t₁ :≡ t₂
¬ (k :| t)   = -, k :|̸ t
¬ (k :|̸ t)   = -, k :| t
¬ (p :∧ q)   = -, proj₂ (¬ p) :∨ proj₂ (¬ q)
¬ (p :∨ q)   = -, proj₂ (¬ p) :∧ proj₂ (¬ q)

nnf : ∀ {n φ} → QFree {n} φ → ∃ (NNF {n})
nnf T          = -, T
nnf F          = -, F
nnf (t₁ :< t₂) = -, (:1 :+ t₁ :≤ t₂)
nnf (t₁ :> t₂) = -, (:1 :+ t₂ :≤ t₁)
nnf (t₁ :≤ t₂) = -, t₁ :≤ t₂
nnf (t₁ :≥ t₂) = -, t₂ :≤ t₁
nnf (t₁ :≡ t₂) = -, t₁ :≡ t₂
nnf (k :| t)   = -, k :| t
nnf (:¬ p)     = ¬ proj₂ (nnf p)
nnf (p :∧ q)   = -, proj₂ (nnf p) :∧ proj₂ (nnf q)
nnf (p :∨ q)   = -, proj₂ (nnf p) :∨ proj₂ (nnf q)
nnf (p :→ q)   = -, (proj₂ (¬ proj₂ (nnf p))) :∨ proj₂ (nnf q)

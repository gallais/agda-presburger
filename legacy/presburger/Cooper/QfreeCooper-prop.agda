module Cooper.QfreeCooper-prop where

open import Product
open import Equivalence

open import Representation
open import Properties
open import Properties-prop
open import Semantics

import Normalization.Negation as Neg
import Normalization.Negation-prop as Negp
import Cooper.NnfCooper as NC
import Cooper.NnfCooper-prop as NCp
open import QfreeCooper

import Data.Nat as Nat
open import Data.Integer
import Data.Vec as V
import Data.Product as P

abstract
  Qfree-cooper : ∀ {n} (φ : Qfree (Nat.suc n)) → ex (proj₁ φ ) ⇔ proj₁ (qelim φ)
  Qfree-cooper φ ρ with NC.Nnf-qelim (Neg.nnf φ) | Negp.nnf-sem φ ρ | NCp (nnf φ) ρ
  ... | ψ , Hψ | P._,_ P₁ Q₁ | P._,_ P₂ Q₂ = ?